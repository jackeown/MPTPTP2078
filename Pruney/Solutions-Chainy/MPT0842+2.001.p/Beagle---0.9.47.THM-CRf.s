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
% DateTime   : Thu Dec  3 10:08:35 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 263 expanded)
%              Number of leaves         :   36 ( 104 expanded)
%              Depth                    :    9
%              Number of atoms          :  237 ( 766 expanded)
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

tff(f_106,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_48,axiom,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_48,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1007,plain,(
    ! [C_393,B_394,A_395] :
      ( v5_relat_1(C_393,B_394)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_395,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1016,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_1007])).

tff(c_81,plain,(
    ! [C_159,A_160,B_161] :
      ( v1_relat_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_90,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_81])).

tff(c_1086,plain,(
    ! [A_432,B_433,C_434,D_435] :
      ( k8_relset_1(A_432,B_433,C_434,D_435) = k10_relat_1(C_434,D_435)
      | ~ m1_subset_1(C_434,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1093,plain,(
    ! [D_435] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_435) = k10_relat_1('#skF_9',D_435) ),
    inference(resolution,[status(thm)],[c_48,c_1086])).

tff(c_109,plain,(
    ! [C_170,B_171,A_172] :
      ( v5_relat_1(C_170,B_171)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_118,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_109])).

tff(c_734,plain,(
    ! [A_340,B_341,C_342,D_343] :
      ( k8_relset_1(A_340,B_341,C_342,D_343) = k10_relat_1(C_342,D_343)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(A_340,B_341))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_741,plain,(
    ! [D_343] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_343) = k10_relat_1('#skF_9',D_343) ),
    inference(resolution,[status(thm)],[c_48,c_734])).

tff(c_389,plain,(
    ! [A_258,B_259,C_260,D_261] :
      ( k8_relset_1(A_258,B_259,C_260,D_261) = k10_relat_1(C_260,D_261)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_396,plain,(
    ! [D_261] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_261) = k10_relat_1('#skF_9',D_261) ),
    inference(resolution,[status(thm)],[c_48,c_389])).

tff(c_70,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_91,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_62,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_125,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_66,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_160,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_265,plain,(
    ! [D_219,A_220,B_221,E_222] :
      ( r2_hidden(D_219,k10_relat_1(A_220,B_221))
      | ~ r2_hidden(E_222,B_221)
      | ~ r2_hidden(k4_tarski(D_219,E_222),A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_278,plain,(
    ! [D_223,A_224] :
      ( r2_hidden(D_223,k10_relat_1(A_224,'#skF_7'))
      | ~ r2_hidden(k4_tarski(D_223,'#skF_11'),A_224)
      | ~ v1_relat_1(A_224) ) ),
    inference(resolution,[status(thm)],[c_125,c_265])).

tff(c_281,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_160,c_278])).

tff(c_284,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_281])).

tff(c_226,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( k8_relset_1(A_207,B_208,C_209,D_210) = k10_relat_1(C_209,D_210)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_237,plain,(
    ! [D_210] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_210) = k10_relat_1('#skF_9',D_210) ),
    inference(resolution,[status(thm)],[c_48,c_226])).

tff(c_56,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_154),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_355,plain,(
    ! [F_240] :
      ( ~ r2_hidden(F_240,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_240),'#skF_9')
      | ~ m1_subset_1(F_240,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_237,c_56])).

tff(c_362,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_160,c_355])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_125,c_362])).

tff(c_370,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_398,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_370])).

tff(c_28,plain,(
    ! [B_49,A_48] :
      ( r1_tarski(k2_relat_1(B_49),A_48)
      | ~ v5_relat_1(B_49,A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_412,plain,(
    ! [A_264,B_265,C_266] :
      ( r2_hidden('#skF_5'(A_264,B_265,C_266),k2_relat_1(C_266))
      | ~ r2_hidden(A_264,k10_relat_1(C_266,B_265))
      | ~ v1_relat_1(C_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_152,plain,(
    ! [A_181,C_182,B_183] :
      ( m1_subset_1(A_181,C_182)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(C_182))
      | ~ r2_hidden(A_181,B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    ! [A_181,B_2,A_1] :
      ( m1_subset_1(A_181,B_2)
      | ~ r2_hidden(A_181,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_152])).

tff(c_619,plain,(
    ! [A_306,B_307,C_308,B_309] :
      ( m1_subset_1('#skF_5'(A_306,B_307,C_308),B_309)
      | ~ r1_tarski(k2_relat_1(C_308),B_309)
      | ~ r2_hidden(A_306,k10_relat_1(C_308,B_307))
      | ~ v1_relat_1(C_308) ) ),
    inference(resolution,[status(thm)],[c_412,c_157])).

tff(c_623,plain,(
    ! [A_310,B_311,B_312,A_313] :
      ( m1_subset_1('#skF_5'(A_310,B_311,B_312),A_313)
      | ~ r2_hidden(A_310,k10_relat_1(B_312,B_311))
      | ~ v5_relat_1(B_312,A_313)
      | ~ v1_relat_1(B_312) ) ),
    inference(resolution,[status(thm)],[c_28,c_619])).

tff(c_641,plain,(
    ! [A_313] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_313)
      | ~ v5_relat_1('#skF_9',A_313)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_398,c_623])).

tff(c_655,plain,(
    ! [A_314] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_314)
      | ~ v5_relat_1('#skF_9',A_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_641])).

tff(c_32,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden('#skF_5'(A_50,B_51,C_52),B_51)
      | ~ r2_hidden(A_50,k10_relat_1(C_52,B_51))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden(k4_tarski(A_50,'#skF_5'(A_50,B_51,C_52)),C_52)
      | ~ r2_hidden(A_50,k10_relat_1(C_52,B_51))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_371,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_154),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_431,plain,(
    ! [F_274] :
      ( ~ r2_hidden(F_274,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_274),'#skF_9')
      | ~ m1_subset_1(F_274,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_371,c_64])).

tff(c_435,plain,(
    ! [B_51] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_51,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_51,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_51))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34,c_431])).

tff(c_548,plain,(
    ! [B_292] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_292,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_292,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_292)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_435])).

tff(c_552,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_548])).

tff(c_555,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_398,c_552])).

tff(c_658,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_655,c_555])).

tff(c_684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_658])).

tff(c_685,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_745,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_685])).

tff(c_768,plain,(
    ! [A_351,B_352,C_353] :
      ( r2_hidden('#skF_5'(A_351,B_352,C_353),k2_relat_1(C_353))
      | ~ r2_hidden(A_351,k10_relat_1(C_353,B_352))
      | ~ v1_relat_1(C_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_714,plain,(
    ! [A_320,C_321,B_322] :
      ( m1_subset_1(A_320,C_321)
      | ~ m1_subset_1(B_322,k1_zfmisc_1(C_321))
      | ~ r2_hidden(A_320,B_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_719,plain,(
    ! [A_320,B_2,A_1] :
      ( m1_subset_1(A_320,B_2)
      | ~ r2_hidden(A_320,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_714])).

tff(c_932,plain,(
    ! [A_380,B_381,C_382,B_383] :
      ( m1_subset_1('#skF_5'(A_380,B_381,C_382),B_383)
      | ~ r1_tarski(k2_relat_1(C_382),B_383)
      | ~ r2_hidden(A_380,k10_relat_1(C_382,B_381))
      | ~ v1_relat_1(C_382) ) ),
    inference(resolution,[status(thm)],[c_768,c_719])).

tff(c_944,plain,(
    ! [A_385,B_386,B_387,A_388] :
      ( m1_subset_1('#skF_5'(A_385,B_386,B_387),A_388)
      | ~ r2_hidden(A_385,k10_relat_1(B_387,B_386))
      | ~ v5_relat_1(B_387,A_388)
      | ~ v1_relat_1(B_387) ) ),
    inference(resolution,[status(thm)],[c_28,c_932])).

tff(c_957,plain,(
    ! [A_388] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_388)
      | ~ v5_relat_1('#skF_9',A_388)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_745,c_944])).

tff(c_969,plain,(
    ! [A_389] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_389)
      | ~ v5_relat_1('#skF_9',A_389) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_957])).

tff(c_790,plain,(
    ! [A_360,B_361,C_362] :
      ( r2_hidden(k4_tarski(A_360,'#skF_5'(A_360,B_361,C_362)),C_362)
      | ~ r2_hidden(A_360,k10_relat_1(C_362,B_361))
      | ~ v1_relat_1(C_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_686,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_154),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_742,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_154),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_686,c_60])).

tff(c_796,plain,(
    ! [B_361] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_361,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_361,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_361))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_790,c_742])).

tff(c_885,plain,(
    ! [B_374] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_374,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_374,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_374)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_796])).

tff(c_889,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_885])).

tff(c_892,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_745,c_889])).

tff(c_972,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_969,c_892])).

tff(c_998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_972])).

tff(c_999,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1095,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_999])).

tff(c_1082,plain,(
    ! [A_429,B_430,C_431] :
      ( r2_hidden('#skF_5'(A_429,B_430,C_431),k2_relat_1(C_431))
      | ~ r2_hidden(A_429,k10_relat_1(C_431,B_430))
      | ~ v1_relat_1(C_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1050,plain,(
    ! [A_406,C_407,B_408] :
      ( m1_subset_1(A_406,C_407)
      | ~ m1_subset_1(B_408,k1_zfmisc_1(C_407))
      | ~ r2_hidden(A_406,B_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1055,plain,(
    ! [A_406,B_2,A_1] :
      ( m1_subset_1(A_406,B_2)
      | ~ r2_hidden(A_406,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_1050])).

tff(c_1285,plain,(
    ! [A_472,B_473,C_474,B_475] :
      ( m1_subset_1('#skF_5'(A_472,B_473,C_474),B_475)
      | ~ r1_tarski(k2_relat_1(C_474),B_475)
      | ~ r2_hidden(A_472,k10_relat_1(C_474,B_473))
      | ~ v1_relat_1(C_474) ) ),
    inference(resolution,[status(thm)],[c_1082,c_1055])).

tff(c_1289,plain,(
    ! [A_476,B_477,B_478,A_479] :
      ( m1_subset_1('#skF_5'(A_476,B_477,B_478),A_479)
      | ~ r2_hidden(A_476,k10_relat_1(B_478,B_477))
      | ~ v5_relat_1(B_478,A_479)
      | ~ v1_relat_1(B_478) ) ),
    inference(resolution,[status(thm)],[c_28,c_1285])).

tff(c_1302,plain,(
    ! [A_479] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_479)
      | ~ v5_relat_1('#skF_9',A_479)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1095,c_1289])).

tff(c_1314,plain,(
    ! [A_480] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_480)
      | ~ v5_relat_1('#skF_9',A_480) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1302])).

tff(c_1130,plain,(
    ! [A_447,B_448,C_449] :
      ( r2_hidden(k4_tarski(A_447,'#skF_5'(A_447,B_448,C_449)),C_449)
      | ~ r2_hidden(A_447,k10_relat_1(C_449,B_448))
      | ~ v1_relat_1(C_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1000,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_68,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_154),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1108,plain,(
    ! [F_154] :
      ( ~ r2_hidden(F_154,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_154),'#skF_9')
      | ~ m1_subset_1(F_154,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1000,c_68])).

tff(c_1136,plain,(
    ! [B_448] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_448,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_448,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_448))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1130,c_1108])).

tff(c_1238,plain,(
    ! [B_466] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_466,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_466,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_466)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1136])).

tff(c_1242,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_1238])).

tff(c_1245,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1095,c_1242])).

tff(c_1317,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1314,c_1245])).

tff(c_1343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_1317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.66  
% 3.52/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.67  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.58/1.67  
% 3.58/1.67  %Foreground sorts:
% 3.58/1.67  
% 3.58/1.67  
% 3.58/1.67  %Background operators:
% 3.58/1.67  
% 3.58/1.67  
% 3.58/1.67  %Foreground operators:
% 3.58/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.58/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.67  tff('#skF_11', type, '#skF_11': $i).
% 3.58/1.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.58/1.67  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.58/1.67  tff('#skF_7', type, '#skF_7': $i).
% 3.58/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.58/1.67  tff('#skF_10', type, '#skF_10': $i).
% 3.58/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.58/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.58/1.67  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.58/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.58/1.67  tff('#skF_9', type, '#skF_9': $i).
% 3.58/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.58/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.67  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.58/1.67  tff('#skF_8', type, '#skF_8': $i).
% 3.58/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.58/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.58/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.58/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.58/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.67  
% 3.58/1.69  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 3.58/1.69  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.58/1.69  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.58/1.69  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.58/1.69  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 3.58/1.69  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.58/1.69  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 3.58/1.69  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.58/1.69  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.58/1.69  tff(c_48, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.58/1.69  tff(c_1007, plain, (![C_393, B_394, A_395]: (v5_relat_1(C_393, B_394) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_395, B_394))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.58/1.69  tff(c_1016, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_48, c_1007])).
% 3.58/1.69  tff(c_81, plain, (![C_159, A_160, B_161]: (v1_relat_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.58/1.69  tff(c_90, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_81])).
% 3.58/1.69  tff(c_1086, plain, (![A_432, B_433, C_434, D_435]: (k8_relset_1(A_432, B_433, C_434, D_435)=k10_relat_1(C_434, D_435) | ~m1_subset_1(C_434, k1_zfmisc_1(k2_zfmisc_1(A_432, B_433))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.58/1.69  tff(c_1093, plain, (![D_435]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_435)=k10_relat_1('#skF_9', D_435))), inference(resolution, [status(thm)], [c_48, c_1086])).
% 3.58/1.69  tff(c_109, plain, (![C_170, B_171, A_172]: (v5_relat_1(C_170, B_171) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.58/1.69  tff(c_118, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_48, c_109])).
% 3.58/1.69  tff(c_734, plain, (![A_340, B_341, C_342, D_343]: (k8_relset_1(A_340, B_341, C_342, D_343)=k10_relat_1(C_342, D_343) | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(A_340, B_341))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.58/1.69  tff(c_741, plain, (![D_343]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_343)=k10_relat_1('#skF_9', D_343))), inference(resolution, [status(thm)], [c_48, c_734])).
% 3.58/1.69  tff(c_389, plain, (![A_258, B_259, C_260, D_261]: (k8_relset_1(A_258, B_259, C_260, D_261)=k10_relat_1(C_260, D_261) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.58/1.69  tff(c_396, plain, (![D_261]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_261)=k10_relat_1('#skF_9', D_261))), inference(resolution, [status(thm)], [c_48, c_389])).
% 3.58/1.69  tff(c_70, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.58/1.69  tff(c_91, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_70])).
% 3.58/1.69  tff(c_62, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.58/1.69  tff(c_125, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_62])).
% 3.58/1.69  tff(c_66, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.58/1.69  tff(c_160, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_66])).
% 3.58/1.69  tff(c_265, plain, (![D_219, A_220, B_221, E_222]: (r2_hidden(D_219, k10_relat_1(A_220, B_221)) | ~r2_hidden(E_222, B_221) | ~r2_hidden(k4_tarski(D_219, E_222), A_220) | ~v1_relat_1(A_220))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.58/1.69  tff(c_278, plain, (![D_223, A_224]: (r2_hidden(D_223, k10_relat_1(A_224, '#skF_7')) | ~r2_hidden(k4_tarski(D_223, '#skF_11'), A_224) | ~v1_relat_1(A_224))), inference(resolution, [status(thm)], [c_125, c_265])).
% 3.58/1.69  tff(c_281, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_160, c_278])).
% 3.58/1.69  tff(c_284, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_281])).
% 3.58/1.69  tff(c_226, plain, (![A_207, B_208, C_209, D_210]: (k8_relset_1(A_207, B_208, C_209, D_210)=k10_relat_1(C_209, D_210) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.58/1.69  tff(c_237, plain, (![D_210]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_210)=k10_relat_1('#skF_9', D_210))), inference(resolution, [status(thm)], [c_48, c_226])).
% 3.58/1.69  tff(c_56, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_154), '#skF_9') | ~m1_subset_1(F_154, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.58/1.69  tff(c_355, plain, (![F_240]: (~r2_hidden(F_240, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_240), '#skF_9') | ~m1_subset_1(F_240, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_237, c_56])).
% 3.58/1.69  tff(c_362, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_160, c_355])).
% 3.58/1.69  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_125, c_362])).
% 3.58/1.69  tff(c_370, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_66])).
% 3.58/1.69  tff(c_398, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_370])).
% 3.58/1.69  tff(c_28, plain, (![B_49, A_48]: (r1_tarski(k2_relat_1(B_49), A_48) | ~v5_relat_1(B_49, A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.58/1.69  tff(c_412, plain, (![A_264, B_265, C_266]: (r2_hidden('#skF_5'(A_264, B_265, C_266), k2_relat_1(C_266)) | ~r2_hidden(A_264, k10_relat_1(C_266, B_265)) | ~v1_relat_1(C_266))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.58/1.69  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.58/1.69  tff(c_152, plain, (![A_181, C_182, B_183]: (m1_subset_1(A_181, C_182) | ~m1_subset_1(B_183, k1_zfmisc_1(C_182)) | ~r2_hidden(A_181, B_183))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.58/1.69  tff(c_157, plain, (![A_181, B_2, A_1]: (m1_subset_1(A_181, B_2) | ~r2_hidden(A_181, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_152])).
% 3.58/1.69  tff(c_619, plain, (![A_306, B_307, C_308, B_309]: (m1_subset_1('#skF_5'(A_306, B_307, C_308), B_309) | ~r1_tarski(k2_relat_1(C_308), B_309) | ~r2_hidden(A_306, k10_relat_1(C_308, B_307)) | ~v1_relat_1(C_308))), inference(resolution, [status(thm)], [c_412, c_157])).
% 3.58/1.69  tff(c_623, plain, (![A_310, B_311, B_312, A_313]: (m1_subset_1('#skF_5'(A_310, B_311, B_312), A_313) | ~r2_hidden(A_310, k10_relat_1(B_312, B_311)) | ~v5_relat_1(B_312, A_313) | ~v1_relat_1(B_312))), inference(resolution, [status(thm)], [c_28, c_619])).
% 3.58/1.69  tff(c_641, plain, (![A_313]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_313) | ~v5_relat_1('#skF_9', A_313) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_398, c_623])).
% 3.58/1.69  tff(c_655, plain, (![A_314]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_314) | ~v5_relat_1('#skF_9', A_314))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_641])).
% 3.58/1.69  tff(c_32, plain, (![A_50, B_51, C_52]: (r2_hidden('#skF_5'(A_50, B_51, C_52), B_51) | ~r2_hidden(A_50, k10_relat_1(C_52, B_51)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.58/1.69  tff(c_34, plain, (![A_50, B_51, C_52]: (r2_hidden(k4_tarski(A_50, '#skF_5'(A_50, B_51, C_52)), C_52) | ~r2_hidden(A_50, k10_relat_1(C_52, B_51)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.58/1.69  tff(c_371, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_66])).
% 3.58/1.69  tff(c_64, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_154), '#skF_9') | ~m1_subset_1(F_154, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.58/1.69  tff(c_431, plain, (![F_274]: (~r2_hidden(F_274, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_274), '#skF_9') | ~m1_subset_1(F_274, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_371, c_64])).
% 3.58/1.69  tff(c_435, plain, (![B_51]: (~r2_hidden('#skF_5'('#skF_10', B_51, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_51, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_51)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_34, c_431])).
% 3.58/1.69  tff(c_548, plain, (![B_292]: (~r2_hidden('#skF_5'('#skF_10', B_292, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_292, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_292)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_435])).
% 3.58/1.69  tff(c_552, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_548])).
% 3.58/1.69  tff(c_555, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_398, c_552])).
% 3.58/1.69  tff(c_658, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_655, c_555])).
% 3.58/1.69  tff(c_684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_658])).
% 3.58/1.69  tff(c_685, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_62])).
% 3.58/1.69  tff(c_745, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_741, c_685])).
% 3.58/1.69  tff(c_768, plain, (![A_351, B_352, C_353]: (r2_hidden('#skF_5'(A_351, B_352, C_353), k2_relat_1(C_353)) | ~r2_hidden(A_351, k10_relat_1(C_353, B_352)) | ~v1_relat_1(C_353))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.58/1.69  tff(c_714, plain, (![A_320, C_321, B_322]: (m1_subset_1(A_320, C_321) | ~m1_subset_1(B_322, k1_zfmisc_1(C_321)) | ~r2_hidden(A_320, B_322))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.58/1.69  tff(c_719, plain, (![A_320, B_2, A_1]: (m1_subset_1(A_320, B_2) | ~r2_hidden(A_320, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_714])).
% 3.58/1.69  tff(c_932, plain, (![A_380, B_381, C_382, B_383]: (m1_subset_1('#skF_5'(A_380, B_381, C_382), B_383) | ~r1_tarski(k2_relat_1(C_382), B_383) | ~r2_hidden(A_380, k10_relat_1(C_382, B_381)) | ~v1_relat_1(C_382))), inference(resolution, [status(thm)], [c_768, c_719])).
% 3.58/1.69  tff(c_944, plain, (![A_385, B_386, B_387, A_388]: (m1_subset_1('#skF_5'(A_385, B_386, B_387), A_388) | ~r2_hidden(A_385, k10_relat_1(B_387, B_386)) | ~v5_relat_1(B_387, A_388) | ~v1_relat_1(B_387))), inference(resolution, [status(thm)], [c_28, c_932])).
% 3.58/1.69  tff(c_957, plain, (![A_388]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_388) | ~v5_relat_1('#skF_9', A_388) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_745, c_944])).
% 3.58/1.69  tff(c_969, plain, (![A_389]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_389) | ~v5_relat_1('#skF_9', A_389))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_957])).
% 3.58/1.69  tff(c_790, plain, (![A_360, B_361, C_362]: (r2_hidden(k4_tarski(A_360, '#skF_5'(A_360, B_361, C_362)), C_362) | ~r2_hidden(A_360, k10_relat_1(C_362, B_361)) | ~v1_relat_1(C_362))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.58/1.69  tff(c_686, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 3.58/1.69  tff(c_60, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_154), '#skF_9') | ~m1_subset_1(F_154, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.58/1.69  tff(c_742, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_154), '#skF_9') | ~m1_subset_1(F_154, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_686, c_60])).
% 3.58/1.69  tff(c_796, plain, (![B_361]: (~r2_hidden('#skF_5'('#skF_10', B_361, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_361, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_361)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_790, c_742])).
% 3.58/1.69  tff(c_885, plain, (![B_374]: (~r2_hidden('#skF_5'('#skF_10', B_374, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_374, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_374)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_796])).
% 3.58/1.69  tff(c_889, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_885])).
% 3.58/1.69  tff(c_892, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_745, c_889])).
% 3.58/1.69  tff(c_972, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_969, c_892])).
% 3.58/1.69  tff(c_998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_972])).
% 3.58/1.69  tff(c_999, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_70])).
% 3.58/1.69  tff(c_1095, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_999])).
% 3.58/1.69  tff(c_1082, plain, (![A_429, B_430, C_431]: (r2_hidden('#skF_5'(A_429, B_430, C_431), k2_relat_1(C_431)) | ~r2_hidden(A_429, k10_relat_1(C_431, B_430)) | ~v1_relat_1(C_431))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.58/1.69  tff(c_1050, plain, (![A_406, C_407, B_408]: (m1_subset_1(A_406, C_407) | ~m1_subset_1(B_408, k1_zfmisc_1(C_407)) | ~r2_hidden(A_406, B_408))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.58/1.69  tff(c_1055, plain, (![A_406, B_2, A_1]: (m1_subset_1(A_406, B_2) | ~r2_hidden(A_406, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_1050])).
% 3.58/1.69  tff(c_1285, plain, (![A_472, B_473, C_474, B_475]: (m1_subset_1('#skF_5'(A_472, B_473, C_474), B_475) | ~r1_tarski(k2_relat_1(C_474), B_475) | ~r2_hidden(A_472, k10_relat_1(C_474, B_473)) | ~v1_relat_1(C_474))), inference(resolution, [status(thm)], [c_1082, c_1055])).
% 3.58/1.69  tff(c_1289, plain, (![A_476, B_477, B_478, A_479]: (m1_subset_1('#skF_5'(A_476, B_477, B_478), A_479) | ~r2_hidden(A_476, k10_relat_1(B_478, B_477)) | ~v5_relat_1(B_478, A_479) | ~v1_relat_1(B_478))), inference(resolution, [status(thm)], [c_28, c_1285])).
% 3.58/1.69  tff(c_1302, plain, (![A_479]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_479) | ~v5_relat_1('#skF_9', A_479) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1095, c_1289])).
% 3.58/1.69  tff(c_1314, plain, (![A_480]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_480) | ~v5_relat_1('#skF_9', A_480))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1302])).
% 3.58/1.69  tff(c_1130, plain, (![A_447, B_448, C_449]: (r2_hidden(k4_tarski(A_447, '#skF_5'(A_447, B_448, C_449)), C_449) | ~r2_hidden(A_447, k10_relat_1(C_449, B_448)) | ~v1_relat_1(C_449))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.58/1.69  tff(c_1000, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 3.58/1.69  tff(c_68, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_154), '#skF_9') | ~m1_subset_1(F_154, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.58/1.69  tff(c_1108, plain, (![F_154]: (~r2_hidden(F_154, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_154), '#skF_9') | ~m1_subset_1(F_154, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1000, c_68])).
% 3.58/1.69  tff(c_1136, plain, (![B_448]: (~r2_hidden('#skF_5'('#skF_10', B_448, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_448, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_448)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1130, c_1108])).
% 3.58/1.69  tff(c_1238, plain, (![B_466]: (~r2_hidden('#skF_5'('#skF_10', B_466, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_466, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_466)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1136])).
% 3.58/1.69  tff(c_1242, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_32, c_1238])).
% 3.58/1.69  tff(c_1245, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1095, c_1242])).
% 3.58/1.69  tff(c_1317, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1314, c_1245])).
% 3.58/1.69  tff(c_1343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1016, c_1317])).
% 3.58/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.69  
% 3.58/1.69  Inference rules
% 3.58/1.69  ----------------------
% 3.58/1.69  #Ref     : 0
% 3.58/1.69  #Sup     : 273
% 3.58/1.69  #Fact    : 0
% 3.58/1.69  #Define  : 0
% 3.58/1.69  #Split   : 7
% 3.58/1.69  #Chain   : 0
% 3.58/1.69  #Close   : 0
% 3.58/1.69  
% 3.58/1.69  Ordering : KBO
% 3.58/1.69  
% 3.58/1.69  Simplification rules
% 3.58/1.69  ----------------------
% 3.58/1.69  #Subsume      : 33
% 3.58/1.69  #Demod        : 61
% 3.58/1.69  #Tautology    : 32
% 3.58/1.69  #SimpNegUnit  : 3
% 3.58/1.69  #BackRed      : 6
% 3.58/1.69  
% 3.58/1.69  #Partial instantiations: 0
% 3.58/1.69  #Strategies tried      : 1
% 3.58/1.69  
% 3.58/1.69  Timing (in seconds)
% 3.58/1.69  ----------------------
% 3.58/1.69  Preprocessing        : 0.34
% 3.58/1.69  Parsing              : 0.16
% 3.58/1.69  CNF conversion       : 0.03
% 3.58/1.69  Main loop            : 0.46
% 3.58/1.69  Inferencing          : 0.17
% 3.58/1.69  Reduction            : 0.13
% 3.58/1.69  Demodulation         : 0.09
% 3.58/1.69  BG Simplification    : 0.03
% 3.58/1.69  Subsumption          : 0.09
% 3.58/1.69  Abstraction          : 0.03
% 3.58/1.69  MUC search           : 0.00
% 3.58/1.69  Cooper               : 0.00
% 3.58/1.69  Total                : 0.86
% 3.58/1.69  Index Insertion      : 0.00
% 3.58/1.69  Index Deletion       : 0.00
% 3.58/1.69  Index Matching       : 0.00
% 3.58/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
