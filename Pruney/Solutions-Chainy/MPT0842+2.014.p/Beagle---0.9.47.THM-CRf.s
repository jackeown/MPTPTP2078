%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:37 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 293 expanded)
%              Number of leaves         :   37 ( 114 expanded)
%              Depth                    :    9
%              Number of atoms          :  249 ( 826 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_111,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_50,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1071,plain,(
    ! [C_407,B_408,A_409] :
      ( v5_relat_1(C_407,B_408)
      | ~ m1_subset_1(C_407,k1_zfmisc_1(k2_zfmisc_1(A_409,B_408))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1080,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_1071])).

tff(c_32,plain,(
    ! [A_53,B_54] : v1_relat_1(k2_zfmisc_1(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1060,plain,(
    ! [B_405,A_406] :
      ( v1_relat_1(B_405)
      | ~ m1_subset_1(B_405,k1_zfmisc_1(A_406))
      | ~ v1_relat_1(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1066,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_50,c_1060])).

tff(c_1070,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1066])).

tff(c_1158,plain,(
    ! [A_444,B_445,C_446,D_447] :
      ( k8_relset_1(A_444,B_445,C_446,D_447) = k10_relat_1(C_446,D_447)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_444,B_445))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1165,plain,(
    ! [D_447] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_447) = k10_relat_1('#skF_9',D_447) ),
    inference(resolution,[status(thm)],[c_50,c_1158])).

tff(c_103,plain,(
    ! [C_167,B_168,A_169] :
      ( v5_relat_1(C_167,B_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_169,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_112,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_103])).

tff(c_85,plain,(
    ! [B_163,A_164] :
      ( v1_relat_1(B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(A_164))
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_50,c_85])).

tff(c_95,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_91])).

tff(c_739,plain,(
    ! [A_331,B_332,C_333,D_334] :
      ( k8_relset_1(A_331,B_332,C_333,D_334) = k10_relat_1(C_333,D_334)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_750,plain,(
    ! [D_334] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_334) = k10_relat_1('#skF_9',D_334) ),
    inference(resolution,[status(thm)],[c_50,c_739])).

tff(c_362,plain,(
    ! [A_256,B_257,C_258,D_259] :
      ( k8_relset_1(A_256,B_257,C_258,D_259) = k10_relat_1(C_258,D_259)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_369,plain,(
    ! [D_259] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_259) = k10_relat_1('#skF_9',D_259) ),
    inference(resolution,[status(thm)],[c_50,c_362])).

tff(c_72,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_139,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_64,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_84,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_68,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_163,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_276,plain,(
    ! [D_223,A_224,B_225,E_226] :
      ( r2_hidden(D_223,k10_relat_1(A_224,B_225))
      | ~ r2_hidden(E_226,B_225)
      | ~ r2_hidden(k4_tarski(D_223,E_226),A_224)
      | ~ v1_relat_1(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_289,plain,(
    ! [D_227,A_228] :
      ( r2_hidden(D_227,k10_relat_1(A_228,'#skF_7'))
      | ~ r2_hidden(k4_tarski(D_227,'#skF_11'),A_228)
      | ~ v1_relat_1(A_228) ) ),
    inference(resolution,[status(thm)],[c_84,c_276])).

tff(c_292,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_163,c_289])).

tff(c_295,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_292])).

tff(c_232,plain,(
    ! [A_209,B_210,C_211,D_212] :
      ( k8_relset_1(A_209,B_210,C_211,D_212) = k10_relat_1(C_211,D_212)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_243,plain,(
    ! [D_212] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_212) = k10_relat_1('#skF_9',D_212) ),
    inference(resolution,[status(thm)],[c_50,c_232])).

tff(c_58,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_317,plain,(
    ! [F_235] :
      ( ~ r2_hidden(F_235,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_235),'#skF_9')
      | ~ m1_subset_1(F_235,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_243,c_58])).

tff(c_324,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_163,c_317])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_84,c_324])).

tff(c_332,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_372,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_332])).

tff(c_30,plain,(
    ! [B_52,A_51] :
      ( r1_tarski(k2_relat_1(B_52),A_51)
      | ~ v5_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_358,plain,(
    ! [A_253,B_254,C_255] :
      ( r2_hidden('#skF_5'(A_253,B_254,C_255),k2_relat_1(C_255))
      | ~ r2_hidden(A_253,k10_relat_1(C_255,B_254))
      | ~ v1_relat_1(C_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_183,C_184,B_185] :
      ( m1_subset_1(A_183,C_184)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(C_184))
      | ~ r2_hidden(A_183,B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_161,plain,(
    ! [A_183,B_2,A_1] :
      ( m1_subset_1(A_183,B_2)
      | ~ r2_hidden(A_183,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_156])).

tff(c_550,plain,(
    ! [A_298,B_299,C_300,B_301] :
      ( m1_subset_1('#skF_5'(A_298,B_299,C_300),B_301)
      | ~ r1_tarski(k2_relat_1(C_300),B_301)
      | ~ r2_hidden(A_298,k10_relat_1(C_300,B_299))
      | ~ v1_relat_1(C_300) ) ),
    inference(resolution,[status(thm)],[c_358,c_161])).

tff(c_554,plain,(
    ! [A_302,B_303,B_304,A_305] :
      ( m1_subset_1('#skF_5'(A_302,B_303,B_304),A_305)
      | ~ r2_hidden(A_302,k10_relat_1(B_304,B_303))
      | ~ v5_relat_1(B_304,A_305)
      | ~ v1_relat_1(B_304) ) ),
    inference(resolution,[status(thm)],[c_30,c_550])).

tff(c_564,plain,(
    ! [A_305] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_305)
      | ~ v5_relat_1('#skF_9',A_305)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_372,c_554])).

tff(c_612,plain,(
    ! [A_309] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_309)
      | ~ v5_relat_1('#skF_9',A_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_564])).

tff(c_36,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden('#skF_5'(A_55,B_56,C_57),B_56)
      | ~ r2_hidden(A_55,k10_relat_1(C_57,B_56))
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_423,plain,(
    ! [A_275,B_276,C_277] :
      ( r2_hidden(k4_tarski(A_275,'#skF_5'(A_275,B_276,C_277)),C_277)
      | ~ r2_hidden(A_275,k10_relat_1(C_277,B_276))
      | ~ v1_relat_1(C_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_333,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_386,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_333,c_66])).

tff(c_429,plain,(
    ! [B_276] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_276,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_276,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_276))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_423,c_386])).

tff(c_525,plain,(
    ! [B_295] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_295,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_295,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_295)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_429])).

tff(c_529,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_525])).

tff(c_532,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_372,c_529])).

tff(c_615,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_612,c_532])).

tff(c_641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_615])).

tff(c_642,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_751,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_642])).

tff(c_770,plain,(
    ! [A_341,B_342,C_343] :
      ( r2_hidden('#skF_5'(A_341,B_342,C_343),k2_relat_1(C_343))
      | ~ r2_hidden(A_341,k10_relat_1(C_343,B_342))
      | ~ v1_relat_1(C_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_661,plain,(
    ! [A_315,C_316,B_317] :
      ( m1_subset_1(A_315,C_316)
      | ~ m1_subset_1(B_317,k1_zfmisc_1(C_316))
      | ~ r2_hidden(A_315,B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_666,plain,(
    ! [A_315,B_2,A_1] :
      ( m1_subset_1(A_315,B_2)
      | ~ r2_hidden(A_315,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_661])).

tff(c_998,plain,(
    ! [A_393,B_394,C_395,B_396] :
      ( m1_subset_1('#skF_5'(A_393,B_394,C_395),B_396)
      | ~ r1_tarski(k2_relat_1(C_395),B_396)
      | ~ r2_hidden(A_393,k10_relat_1(C_395,B_394))
      | ~ v1_relat_1(C_395) ) ),
    inference(resolution,[status(thm)],[c_770,c_666])).

tff(c_1002,plain,(
    ! [A_397,B_398,B_399,A_400] :
      ( m1_subset_1('#skF_5'(A_397,B_398,B_399),A_400)
      | ~ r2_hidden(A_397,k10_relat_1(B_399,B_398))
      | ~ v5_relat_1(B_399,A_400)
      | ~ v1_relat_1(B_399) ) ),
    inference(resolution,[status(thm)],[c_30,c_998])).

tff(c_1015,plain,(
    ! [A_400] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_400)
      | ~ v5_relat_1('#skF_9',A_400)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_751,c_1002])).

tff(c_1028,plain,(
    ! [A_404] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_404)
      | ~ v5_relat_1('#skF_9',A_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1015])).

tff(c_812,plain,(
    ! [A_361,B_362,C_363] :
      ( r2_hidden(k4_tarski(A_361,'#skF_5'(A_361,B_362,C_363)),C_363)
      | ~ r2_hidden(A_361,k10_relat_1(C_363,B_362))
      | ~ v1_relat_1(C_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_643,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_70,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_684,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_70])).

tff(c_821,plain,(
    ! [B_362] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_362,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_362,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_362))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_812,c_684])).

tff(c_946,plain,(
    ! [B_385] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_385,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_385,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_385)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_821])).

tff(c_950,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_946])).

tff(c_953,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_751,c_950])).

tff(c_1031,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1028,c_953])).

tff(c_1057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1031])).

tff(c_1058,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1167,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1165,c_1058])).

tff(c_1407,plain,(
    ! [A_501,B_502,C_503] :
      ( r2_hidden('#skF_5'(A_501,B_502,C_503),k2_relat_1(C_503))
      | ~ r2_hidden(A_501,k10_relat_1(C_503,B_502))
      | ~ v1_relat_1(C_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1131,plain,(
    ! [A_425,C_426,B_427] :
      ( m1_subset_1(A_425,C_426)
      | ~ m1_subset_1(B_427,k1_zfmisc_1(C_426))
      | ~ r2_hidden(A_425,B_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1136,plain,(
    ! [A_425,B_2,A_1] :
      ( m1_subset_1(A_425,B_2)
      | ~ r2_hidden(A_425,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_1131])).

tff(c_1557,plain,(
    ! [A_534,B_535,C_536,B_537] :
      ( m1_subset_1('#skF_5'(A_534,B_535,C_536),B_537)
      | ~ r1_tarski(k2_relat_1(C_536),B_537)
      | ~ r2_hidden(A_534,k10_relat_1(C_536,B_535))
      | ~ v1_relat_1(C_536) ) ),
    inference(resolution,[status(thm)],[c_1407,c_1136])).

tff(c_1561,plain,(
    ! [A_538,B_539,B_540,A_541] :
      ( m1_subset_1('#skF_5'(A_538,B_539,B_540),A_541)
      | ~ r2_hidden(A_538,k10_relat_1(B_540,B_539))
      | ~ v5_relat_1(B_540,A_541)
      | ~ v1_relat_1(B_540) ) ),
    inference(resolution,[status(thm)],[c_30,c_1557])).

tff(c_1571,plain,(
    ! [A_541] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_541)
      | ~ v5_relat_1('#skF_9',A_541)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1167,c_1561])).

tff(c_1582,plain,(
    ! [A_542] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_542)
      | ~ v5_relat_1('#skF_9',A_542) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1070,c_1571])).

tff(c_1430,plain,(
    ! [A_511,B_512,C_513] :
      ( r2_hidden(k4_tarski(A_511,'#skF_5'(A_511,B_512,C_513)),C_513)
      | ~ r2_hidden(A_511,k10_relat_1(C_513,B_512))
      | ~ v1_relat_1(C_513) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1059,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1411,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1059,c_62])).

tff(c_1436,plain,(
    ! [B_512] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_512,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_512,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_512))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1430,c_1411])).

tff(c_1525,plain,(
    ! [B_526] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_526,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_526,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_526)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1070,c_1436])).

tff(c_1529,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_1525])).

tff(c_1532,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1070,c_1167,c_1529])).

tff(c_1585,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1582,c_1532])).

tff(c_1611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_1585])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:36:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.65  
% 3.86/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.66  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.86/1.66  
% 3.86/1.66  %Foreground sorts:
% 3.86/1.66  
% 3.86/1.66  
% 3.86/1.66  %Background operators:
% 3.86/1.66  
% 3.86/1.66  
% 3.86/1.66  %Foreground operators:
% 3.86/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.86/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.66  tff('#skF_11', type, '#skF_11': $i).
% 3.86/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.86/1.66  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.86/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.86/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.66  tff('#skF_10', type, '#skF_10': $i).
% 3.86/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.86/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.86/1.66  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.86/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.86/1.66  tff('#skF_9', type, '#skF_9': $i).
% 3.86/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.86/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.66  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.86/1.66  tff('#skF_8', type, '#skF_8': $i).
% 3.86/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.86/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.86/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.86/1.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.86/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.86/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.86/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.66  
% 3.86/1.68  tff(f_111, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 3.86/1.68  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.86/1.68  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.86/1.68  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.86/1.68  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.86/1.68  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 3.86/1.68  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.86/1.68  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.86/1.68  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.86/1.68  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.86/1.68  tff(c_50, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.86/1.68  tff(c_1071, plain, (![C_407, B_408, A_409]: (v5_relat_1(C_407, B_408) | ~m1_subset_1(C_407, k1_zfmisc_1(k2_zfmisc_1(A_409, B_408))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.86/1.68  tff(c_1080, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_50, c_1071])).
% 3.86/1.68  tff(c_32, plain, (![A_53, B_54]: (v1_relat_1(k2_zfmisc_1(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.86/1.68  tff(c_1060, plain, (![B_405, A_406]: (v1_relat_1(B_405) | ~m1_subset_1(B_405, k1_zfmisc_1(A_406)) | ~v1_relat_1(A_406))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.86/1.68  tff(c_1066, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_50, c_1060])).
% 3.86/1.68  tff(c_1070, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1066])).
% 3.86/1.68  tff(c_1158, plain, (![A_444, B_445, C_446, D_447]: (k8_relset_1(A_444, B_445, C_446, D_447)=k10_relat_1(C_446, D_447) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_444, B_445))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.86/1.68  tff(c_1165, plain, (![D_447]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_447)=k10_relat_1('#skF_9', D_447))), inference(resolution, [status(thm)], [c_50, c_1158])).
% 3.86/1.68  tff(c_103, plain, (![C_167, B_168, A_169]: (v5_relat_1(C_167, B_168) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_169, B_168))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.86/1.68  tff(c_112, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_50, c_103])).
% 3.86/1.68  tff(c_85, plain, (![B_163, A_164]: (v1_relat_1(B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(A_164)) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.86/1.68  tff(c_91, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_50, c_85])).
% 3.86/1.68  tff(c_95, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_91])).
% 3.86/1.68  tff(c_739, plain, (![A_331, B_332, C_333, D_334]: (k8_relset_1(A_331, B_332, C_333, D_334)=k10_relat_1(C_333, D_334) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.86/1.68  tff(c_750, plain, (![D_334]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_334)=k10_relat_1('#skF_9', D_334))), inference(resolution, [status(thm)], [c_50, c_739])).
% 3.86/1.68  tff(c_362, plain, (![A_256, B_257, C_258, D_259]: (k8_relset_1(A_256, B_257, C_258, D_259)=k10_relat_1(C_258, D_259) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.86/1.68  tff(c_369, plain, (![D_259]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_259)=k10_relat_1('#skF_9', D_259))), inference(resolution, [status(thm)], [c_50, c_362])).
% 3.86/1.68  tff(c_72, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.86/1.68  tff(c_139, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_72])).
% 3.86/1.68  tff(c_64, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.86/1.68  tff(c_84, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_64])).
% 3.86/1.68  tff(c_68, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.86/1.68  tff(c_163, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_68])).
% 3.86/1.68  tff(c_276, plain, (![D_223, A_224, B_225, E_226]: (r2_hidden(D_223, k10_relat_1(A_224, B_225)) | ~r2_hidden(E_226, B_225) | ~r2_hidden(k4_tarski(D_223, E_226), A_224) | ~v1_relat_1(A_224))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.86/1.68  tff(c_289, plain, (![D_227, A_228]: (r2_hidden(D_227, k10_relat_1(A_228, '#skF_7')) | ~r2_hidden(k4_tarski(D_227, '#skF_11'), A_228) | ~v1_relat_1(A_228))), inference(resolution, [status(thm)], [c_84, c_276])).
% 3.86/1.68  tff(c_292, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_163, c_289])).
% 3.86/1.68  tff(c_295, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_292])).
% 3.86/1.68  tff(c_232, plain, (![A_209, B_210, C_211, D_212]: (k8_relset_1(A_209, B_210, C_211, D_212)=k10_relat_1(C_211, D_212) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.86/1.68  tff(c_243, plain, (![D_212]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_212)=k10_relat_1('#skF_9', D_212))), inference(resolution, [status(thm)], [c_50, c_232])).
% 3.86/1.68  tff(c_58, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.86/1.68  tff(c_317, plain, (![F_235]: (~r2_hidden(F_235, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_235), '#skF_9') | ~m1_subset_1(F_235, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_243, c_58])).
% 3.86/1.68  tff(c_324, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_163, c_317])).
% 3.86/1.68  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_84, c_324])).
% 3.86/1.68  tff(c_332, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_68])).
% 3.86/1.68  tff(c_372, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_332])).
% 3.86/1.68  tff(c_30, plain, (![B_52, A_51]: (r1_tarski(k2_relat_1(B_52), A_51) | ~v5_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.86/1.68  tff(c_358, plain, (![A_253, B_254, C_255]: (r2_hidden('#skF_5'(A_253, B_254, C_255), k2_relat_1(C_255)) | ~r2_hidden(A_253, k10_relat_1(C_255, B_254)) | ~v1_relat_1(C_255))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.86/1.68  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.86/1.68  tff(c_156, plain, (![A_183, C_184, B_185]: (m1_subset_1(A_183, C_184) | ~m1_subset_1(B_185, k1_zfmisc_1(C_184)) | ~r2_hidden(A_183, B_185))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.86/1.68  tff(c_161, plain, (![A_183, B_2, A_1]: (m1_subset_1(A_183, B_2) | ~r2_hidden(A_183, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_156])).
% 3.86/1.68  tff(c_550, plain, (![A_298, B_299, C_300, B_301]: (m1_subset_1('#skF_5'(A_298, B_299, C_300), B_301) | ~r1_tarski(k2_relat_1(C_300), B_301) | ~r2_hidden(A_298, k10_relat_1(C_300, B_299)) | ~v1_relat_1(C_300))), inference(resolution, [status(thm)], [c_358, c_161])).
% 3.86/1.68  tff(c_554, plain, (![A_302, B_303, B_304, A_305]: (m1_subset_1('#skF_5'(A_302, B_303, B_304), A_305) | ~r2_hidden(A_302, k10_relat_1(B_304, B_303)) | ~v5_relat_1(B_304, A_305) | ~v1_relat_1(B_304))), inference(resolution, [status(thm)], [c_30, c_550])).
% 3.86/1.68  tff(c_564, plain, (![A_305]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_305) | ~v5_relat_1('#skF_9', A_305) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_372, c_554])).
% 3.86/1.68  tff(c_612, plain, (![A_309]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_309) | ~v5_relat_1('#skF_9', A_309))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_564])).
% 3.86/1.68  tff(c_36, plain, (![A_55, B_56, C_57]: (r2_hidden('#skF_5'(A_55, B_56, C_57), B_56) | ~r2_hidden(A_55, k10_relat_1(C_57, B_56)) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.86/1.68  tff(c_423, plain, (![A_275, B_276, C_277]: (r2_hidden(k4_tarski(A_275, '#skF_5'(A_275, B_276, C_277)), C_277) | ~r2_hidden(A_275, k10_relat_1(C_277, B_276)) | ~v1_relat_1(C_277))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.86/1.68  tff(c_333, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_68])).
% 3.86/1.68  tff(c_66, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.86/1.68  tff(c_386, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_333, c_66])).
% 3.86/1.68  tff(c_429, plain, (![B_276]: (~r2_hidden('#skF_5'('#skF_10', B_276, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_276, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_276)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_423, c_386])).
% 3.86/1.68  tff(c_525, plain, (![B_295]: (~r2_hidden('#skF_5'('#skF_10', B_295, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_295, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_295)))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_429])).
% 3.86/1.68  tff(c_529, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_525])).
% 3.86/1.68  tff(c_532, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_372, c_529])).
% 3.86/1.68  tff(c_615, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_612, c_532])).
% 3.86/1.68  tff(c_641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_615])).
% 3.86/1.68  tff(c_642, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_72])).
% 3.86/1.68  tff(c_751, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_750, c_642])).
% 3.86/1.68  tff(c_770, plain, (![A_341, B_342, C_343]: (r2_hidden('#skF_5'(A_341, B_342, C_343), k2_relat_1(C_343)) | ~r2_hidden(A_341, k10_relat_1(C_343, B_342)) | ~v1_relat_1(C_343))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.86/1.68  tff(c_661, plain, (![A_315, C_316, B_317]: (m1_subset_1(A_315, C_316) | ~m1_subset_1(B_317, k1_zfmisc_1(C_316)) | ~r2_hidden(A_315, B_317))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.86/1.68  tff(c_666, plain, (![A_315, B_2, A_1]: (m1_subset_1(A_315, B_2) | ~r2_hidden(A_315, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_661])).
% 3.86/1.68  tff(c_998, plain, (![A_393, B_394, C_395, B_396]: (m1_subset_1('#skF_5'(A_393, B_394, C_395), B_396) | ~r1_tarski(k2_relat_1(C_395), B_396) | ~r2_hidden(A_393, k10_relat_1(C_395, B_394)) | ~v1_relat_1(C_395))), inference(resolution, [status(thm)], [c_770, c_666])).
% 4.08/1.68  tff(c_1002, plain, (![A_397, B_398, B_399, A_400]: (m1_subset_1('#skF_5'(A_397, B_398, B_399), A_400) | ~r2_hidden(A_397, k10_relat_1(B_399, B_398)) | ~v5_relat_1(B_399, A_400) | ~v1_relat_1(B_399))), inference(resolution, [status(thm)], [c_30, c_998])).
% 4.08/1.68  tff(c_1015, plain, (![A_400]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_400) | ~v5_relat_1('#skF_9', A_400) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_751, c_1002])).
% 4.08/1.68  tff(c_1028, plain, (![A_404]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_404) | ~v5_relat_1('#skF_9', A_404))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_1015])).
% 4.08/1.68  tff(c_812, plain, (![A_361, B_362, C_363]: (r2_hidden(k4_tarski(A_361, '#skF_5'(A_361, B_362, C_363)), C_363) | ~r2_hidden(A_361, k10_relat_1(C_363, B_362)) | ~v1_relat_1(C_363))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.08/1.68  tff(c_643, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_72])).
% 4.08/1.68  tff(c_70, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.08/1.68  tff(c_684, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_643, c_70])).
% 4.08/1.68  tff(c_821, plain, (![B_362]: (~r2_hidden('#skF_5'('#skF_10', B_362, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_362, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_362)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_812, c_684])).
% 4.08/1.68  tff(c_946, plain, (![B_385]: (~r2_hidden('#skF_5'('#skF_10', B_385, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_385, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_385)))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_821])).
% 4.08/1.68  tff(c_950, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_946])).
% 4.08/1.68  tff(c_953, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_751, c_950])).
% 4.08/1.68  tff(c_1031, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1028, c_953])).
% 4.08/1.68  tff(c_1057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_1031])).
% 4.08/1.68  tff(c_1058, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_64])).
% 4.08/1.68  tff(c_1167, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1165, c_1058])).
% 4.08/1.68  tff(c_1407, plain, (![A_501, B_502, C_503]: (r2_hidden('#skF_5'(A_501, B_502, C_503), k2_relat_1(C_503)) | ~r2_hidden(A_501, k10_relat_1(C_503, B_502)) | ~v1_relat_1(C_503))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.08/1.68  tff(c_1131, plain, (![A_425, C_426, B_427]: (m1_subset_1(A_425, C_426) | ~m1_subset_1(B_427, k1_zfmisc_1(C_426)) | ~r2_hidden(A_425, B_427))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.08/1.68  tff(c_1136, plain, (![A_425, B_2, A_1]: (m1_subset_1(A_425, B_2) | ~r2_hidden(A_425, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_1131])).
% 4.08/1.68  tff(c_1557, plain, (![A_534, B_535, C_536, B_537]: (m1_subset_1('#skF_5'(A_534, B_535, C_536), B_537) | ~r1_tarski(k2_relat_1(C_536), B_537) | ~r2_hidden(A_534, k10_relat_1(C_536, B_535)) | ~v1_relat_1(C_536))), inference(resolution, [status(thm)], [c_1407, c_1136])).
% 4.08/1.68  tff(c_1561, plain, (![A_538, B_539, B_540, A_541]: (m1_subset_1('#skF_5'(A_538, B_539, B_540), A_541) | ~r2_hidden(A_538, k10_relat_1(B_540, B_539)) | ~v5_relat_1(B_540, A_541) | ~v1_relat_1(B_540))), inference(resolution, [status(thm)], [c_30, c_1557])).
% 4.08/1.68  tff(c_1571, plain, (![A_541]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_541) | ~v5_relat_1('#skF_9', A_541) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1167, c_1561])).
% 4.08/1.68  tff(c_1582, plain, (![A_542]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_542) | ~v5_relat_1('#skF_9', A_542))), inference(demodulation, [status(thm), theory('equality')], [c_1070, c_1571])).
% 4.08/1.68  tff(c_1430, plain, (![A_511, B_512, C_513]: (r2_hidden(k4_tarski(A_511, '#skF_5'(A_511, B_512, C_513)), C_513) | ~r2_hidden(A_511, k10_relat_1(C_513, B_512)) | ~v1_relat_1(C_513))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.08/1.68  tff(c_1059, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 4.08/1.68  tff(c_62, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.08/1.68  tff(c_1411, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1059, c_62])).
% 4.08/1.68  tff(c_1436, plain, (![B_512]: (~r2_hidden('#skF_5'('#skF_10', B_512, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_512, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_512)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1430, c_1411])).
% 4.08/1.68  tff(c_1525, plain, (![B_526]: (~r2_hidden('#skF_5'('#skF_10', B_526, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_526, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_526)))), inference(demodulation, [status(thm), theory('equality')], [c_1070, c_1436])).
% 4.08/1.68  tff(c_1529, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_1525])).
% 4.08/1.68  tff(c_1532, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1070, c_1167, c_1529])).
% 4.08/1.68  tff(c_1585, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1582, c_1532])).
% 4.08/1.68  tff(c_1611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1080, c_1585])).
% 4.08/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.68  
% 4.08/1.68  Inference rules
% 4.08/1.68  ----------------------
% 4.08/1.68  #Ref     : 0
% 4.08/1.68  #Sup     : 324
% 4.08/1.68  #Fact    : 0
% 4.08/1.68  #Define  : 0
% 4.08/1.68  #Split   : 15
% 4.08/1.68  #Chain   : 0
% 4.08/1.68  #Close   : 0
% 4.08/1.68  
% 4.08/1.68  Ordering : KBO
% 4.08/1.68  
% 4.08/1.68  Simplification rules
% 4.08/1.68  ----------------------
% 4.08/1.68  #Subsume      : 33
% 4.08/1.68  #Demod        : 77
% 4.08/1.68  #Tautology    : 33
% 4.08/1.68  #SimpNegUnit  : 4
% 4.08/1.68  #BackRed      : 5
% 4.08/1.68  
% 4.08/1.68  #Partial instantiations: 0
% 4.08/1.68  #Strategies tried      : 1
% 4.08/1.68  
% 4.08/1.68  Timing (in seconds)
% 4.08/1.68  ----------------------
% 4.08/1.68  Preprocessing        : 0.36
% 4.08/1.68  Parsing              : 0.18
% 4.08/1.68  CNF conversion       : 0.04
% 4.08/1.68  Main loop            : 0.55
% 4.08/1.68  Inferencing          : 0.21
% 4.08/1.68  Reduction            : 0.16
% 4.08/1.68  Demodulation         : 0.11
% 4.08/1.68  BG Simplification    : 0.03
% 4.08/1.68  Subsumption          : 0.10
% 4.08/1.68  Abstraction          : 0.03
% 4.08/1.68  MUC search           : 0.00
% 4.08/1.68  Cooper               : 0.00
% 4.08/1.68  Total                : 0.96
% 4.08/1.69  Index Insertion      : 0.00
% 4.08/1.69  Index Deletion       : 0.00
% 4.08/1.69  Index Matching       : 0.00
% 4.08/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
