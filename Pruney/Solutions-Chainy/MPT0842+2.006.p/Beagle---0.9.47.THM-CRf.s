%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:36 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 270 expanded)
%              Number of leaves         :   34 ( 105 expanded)
%              Depth                    :    9
%              Number of atoms          :  229 ( 781 expanded)
%              Number of equality atoms :   17 (  31 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_42,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_66,plain,(
    ! [C_159,A_160,B_161] :
      ( v1_relat_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_66])).

tff(c_1503,plain,(
    ! [A_422,B_423,C_424,D_425] :
      ( k8_relset_1(A_422,B_423,C_424,D_425) = k10_relat_1(C_424,D_425)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(A_422,B_423))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1510,plain,(
    ! [D_425] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_425) = k10_relat_1('#skF_9',D_425) ),
    inference(resolution,[status(thm)],[c_42,c_1503])).

tff(c_905,plain,(
    ! [A_320,B_321,C_322,D_323] :
      ( k8_relset_1(A_320,B_321,C_322,D_323) = k10_relat_1(C_322,D_323)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_916,plain,(
    ! [D_323] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_323) = k10_relat_1('#skF_9',D_323) ),
    inference(resolution,[status(thm)],[c_42,c_905])).

tff(c_362,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( k8_relset_1(A_223,B_224,C_225,D_226) = k10_relat_1(C_225,D_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_369,plain,(
    ! [D_226] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_226) = k10_relat_1('#skF_9',D_226) ),
    inference(resolution,[status(thm)],[c_42,c_362])).

tff(c_64,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_71,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_56,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_72,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_60,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_91,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_214,plain,(
    ! [D_198,A_199,B_200,E_201] :
      ( r2_hidden(D_198,k10_relat_1(A_199,B_200))
      | ~ r2_hidden(E_201,B_200)
      | ~ r2_hidden(k4_tarski(D_198,E_201),A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_233,plain,(
    ! [D_202,A_203] :
      ( r2_hidden(D_202,k10_relat_1(A_203,'#skF_7'))
      | ~ r2_hidden(k4_tarski(D_202,'#skF_11'),A_203)
      | ~ v1_relat_1(A_203) ) ),
    inference(resolution,[status(thm)],[c_72,c_214])).

tff(c_239,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_91,c_233])).

tff(c_243,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_239])).

tff(c_171,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k8_relset_1(A_184,B_185,C_186,D_187) = k10_relat_1(C_186,D_187)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_182,plain,(
    ! [D_187] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_187) = k10_relat_1('#skF_9',D_187) ),
    inference(resolution,[status(thm)],[c_42,c_171])).

tff(c_50,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_291,plain,(
    ! [F_209] :
      ( ~ r2_hidden(F_209,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_209),'#skF_9')
      | ~ m1_subset_1(F_209,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_182,c_50])).

tff(c_302,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_91,c_291])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_72,c_302])).

tff(c_313,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_372,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_313])).

tff(c_26,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_5'(A_49,B_50,C_51),B_50)
      | ~ r2_hidden(A_49,k10_relat_1(C_51,B_50))
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_433,plain,(
    ! [A_243,B_244,C_245] :
      ( r2_hidden(k4_tarski(A_243,'#skF_5'(A_243,B_244,C_245)),C_245)
      | ~ r2_hidden(A_243,k10_relat_1(C_245,B_244))
      | ~ v1_relat_1(C_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_314,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_409,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_58])).

tff(c_437,plain,(
    ! [B_244] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_244,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_244,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_244))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_433,c_409])).

tff(c_533,plain,(
    ! [B_263] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_263,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_263,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_263)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_437])).

tff(c_541,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_533])).

tff(c_547,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_372,c_541])).

tff(c_82,plain,(
    ! [A_166,B_167,C_168] :
      ( k2_relset_1(A_166,B_167,C_168) = k2_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_86,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_331,plain,(
    ! [A_214,B_215,C_216] :
      ( m1_subset_1(k2_relset_1(A_214,B_215,C_216),k1_zfmisc_1(B_215))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_342,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_331])).

tff(c_346,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_342])).

tff(c_354,plain,(
    ! [A_220,B_221,C_222] :
      ( r2_hidden('#skF_5'(A_220,B_221,C_222),k2_relat_1(C_222))
      | ~ r2_hidden(A_220,k10_relat_1(C_222,B_221))
      | ~ v1_relat_1(C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_708,plain,(
    ! [A_285,B_286,C_287,A_288] :
      ( r2_hidden('#skF_5'(A_285,B_286,C_287),A_288)
      | ~ m1_subset_1(k2_relat_1(C_287),k1_zfmisc_1(A_288))
      | ~ r2_hidden(A_285,k10_relat_1(C_287,B_286))
      | ~ v1_relat_1(C_287) ) ),
    inference(resolution,[status(thm)],[c_354,c_2])).

tff(c_710,plain,(
    ! [A_285,B_286] :
      ( r2_hidden('#skF_5'(A_285,B_286,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_285,k10_relat_1('#skF_9',B_286))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_346,c_708])).

tff(c_731,plain,(
    ! [A_293,B_294] :
      ( r2_hidden('#skF_5'(A_293,B_294,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_293,k10_relat_1('#skF_9',B_294)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_710])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_742,plain,(
    ! [A_295,B_296] :
      ( m1_subset_1('#skF_5'(A_295,B_296,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_295,k10_relat_1('#skF_9',B_296)) ) ),
    inference(resolution,[status(thm)],[c_731,c_4])).

tff(c_773,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_372,c_742])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_773])).

tff(c_791,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_927,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_791])).

tff(c_969,plain,(
    ! [A_336,B_337,C_338] :
      ( r2_hidden(k4_tarski(A_336,'#skF_5'(A_336,B_337,C_338)),C_338)
      | ~ r2_hidden(A_336,k10_relat_1(C_338,B_337))
      | ~ v1_relat_1(C_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_792,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_824,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_792,c_54])).

tff(c_978,plain,(
    ! [B_337] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_337,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_337,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_337))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_969,c_824])).

tff(c_1134,plain,(
    ! [B_367] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_367,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_367,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_367)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_978])).

tff(c_1142,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_1134])).

tff(c_1148,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_927,c_1142])).

tff(c_841,plain,(
    ! [A_306,B_307,C_308] :
      ( k2_relset_1(A_306,B_307,C_308) = k2_relat_1(C_308)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_850,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_841])).

tff(c_863,plain,(
    ! [A_312,B_313,C_314] :
      ( m1_subset_1(k2_relset_1(A_312,B_313,C_314),k1_zfmisc_1(B_313))
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_874,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_863])).

tff(c_878,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_874])).

tff(c_917,plain,(
    ! [A_324,B_325,C_326] :
      ( r2_hidden('#skF_5'(A_324,B_325,C_326),k2_relat_1(C_326))
      | ~ r2_hidden(A_324,k10_relat_1(C_326,B_325))
      | ~ v1_relat_1(C_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1369,plain,(
    ! [A_397,B_398,C_399,A_400] :
      ( r2_hidden('#skF_5'(A_397,B_398,C_399),A_400)
      | ~ m1_subset_1(k2_relat_1(C_399),k1_zfmisc_1(A_400))
      | ~ r2_hidden(A_397,k10_relat_1(C_399,B_398))
      | ~ v1_relat_1(C_399) ) ),
    inference(resolution,[status(thm)],[c_917,c_2])).

tff(c_1371,plain,(
    ! [A_397,B_398] :
      ( r2_hidden('#skF_5'(A_397,B_398,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_397,k10_relat_1('#skF_9',B_398))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_878,c_1369])).

tff(c_1375,plain,(
    ! [A_401,B_402] :
      ( r2_hidden('#skF_5'(A_401,B_402,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_401,k10_relat_1('#skF_9',B_402)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1371])).

tff(c_1386,plain,(
    ! [A_403,B_404] :
      ( m1_subset_1('#skF_5'(A_403,B_404,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_403,k10_relat_1('#skF_9',B_404)) ) ),
    inference(resolution,[status(thm)],[c_1375,c_4])).

tff(c_1421,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_927,c_1386])).

tff(c_1443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1148,c_1421])).

tff(c_1444,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1513,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_1444])).

tff(c_1548,plain,(
    ! [A_432,B_433,C_434] :
      ( r2_hidden(k4_tarski(A_432,'#skF_5'(A_432,B_433,C_434)),C_434)
      | ~ r2_hidden(A_432,k10_relat_1(C_434,B_433))
      | ~ v1_relat_1(C_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1445,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1536,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_156),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1445,c_62])).

tff(c_1552,plain,(
    ! [B_433] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_433,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_433,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_433))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1548,c_1536])).

tff(c_1703,plain,(
    ! [B_468] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_468,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_468,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_468)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1552])).

tff(c_1711,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_1703])).

tff(c_1717,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1513,c_1711])).

tff(c_1464,plain,(
    ! [A_410,B_411,C_412] :
      ( k2_relset_1(A_410,B_411,C_412) = k2_relat_1(C_412)
      | ~ m1_subset_1(C_412,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1468,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_1464])).

tff(c_1474,plain,(
    ! [A_413,B_414,C_415] :
      ( m1_subset_1(k2_relset_1(A_413,B_414,C_415),k1_zfmisc_1(B_414))
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_413,B_414))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1485,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1468,c_1474])).

tff(c_1489,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1485])).

tff(c_1540,plain,(
    ! [A_429,B_430,C_431] :
      ( r2_hidden('#skF_5'(A_429,B_430,C_431),k2_relat_1(C_431))
      | ~ r2_hidden(A_429,k10_relat_1(C_431,B_430))
      | ~ v1_relat_1(C_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1839,plain,(
    ! [A_486,B_487,C_488,A_489] :
      ( r2_hidden('#skF_5'(A_486,B_487,C_488),A_489)
      | ~ m1_subset_1(k2_relat_1(C_488),k1_zfmisc_1(A_489))
      | ~ r2_hidden(A_486,k10_relat_1(C_488,B_487))
      | ~ v1_relat_1(C_488) ) ),
    inference(resolution,[status(thm)],[c_1540,c_2])).

tff(c_1841,plain,(
    ! [A_486,B_487] :
      ( r2_hidden('#skF_5'(A_486,B_487,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_486,k10_relat_1('#skF_9',B_487))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1489,c_1839])).

tff(c_1845,plain,(
    ! [A_490,B_491] :
      ( r2_hidden('#skF_5'(A_490,B_491,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_490,k10_relat_1('#skF_9',B_491)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1841])).

tff(c_1856,plain,(
    ! [A_492,B_493] :
      ( m1_subset_1('#skF_5'(A_492,B_493,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_492,k10_relat_1('#skF_9',B_493)) ) ),
    inference(resolution,[status(thm)],[c_1845,c_4])).

tff(c_1887,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1513,c_1856])).

tff(c_1904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1717,c_1887])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:07:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.86  
% 4.20/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.86  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 4.20/1.86  
% 4.20/1.86  %Foreground sorts:
% 4.20/1.86  
% 4.20/1.86  
% 4.20/1.86  %Background operators:
% 4.20/1.86  
% 4.20/1.86  
% 4.20/1.86  %Foreground operators:
% 4.20/1.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.20/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.20/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.20/1.86  tff('#skF_11', type, '#skF_11': $i).
% 4.20/1.86  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.20/1.86  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.20/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.20/1.86  tff('#skF_10', type, '#skF_10': $i).
% 4.20/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.20/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.20/1.86  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.20/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.20/1.86  tff('#skF_9', type, '#skF_9': $i).
% 4.20/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/1.86  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.20/1.86  tff('#skF_8', type, '#skF_8': $i).
% 4.20/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.86  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.20/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.20/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.20/1.86  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.20/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.20/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.86  
% 4.20/1.88  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 4.20/1.88  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.20/1.88  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.20/1.88  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 4.20/1.88  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 4.20/1.88  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.20/1.88  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.20/1.88  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.20/1.88  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.20/1.88  tff(c_42, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/1.88  tff(c_66, plain, (![C_159, A_160, B_161]: (v1_relat_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.20/1.88  tff(c_70, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_66])).
% 4.20/1.88  tff(c_1503, plain, (![A_422, B_423, C_424, D_425]: (k8_relset_1(A_422, B_423, C_424, D_425)=k10_relat_1(C_424, D_425) | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(A_422, B_423))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.20/1.88  tff(c_1510, plain, (![D_425]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_425)=k10_relat_1('#skF_9', D_425))), inference(resolution, [status(thm)], [c_42, c_1503])).
% 4.20/1.88  tff(c_905, plain, (![A_320, B_321, C_322, D_323]: (k8_relset_1(A_320, B_321, C_322, D_323)=k10_relat_1(C_322, D_323) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.20/1.88  tff(c_916, plain, (![D_323]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_323)=k10_relat_1('#skF_9', D_323))), inference(resolution, [status(thm)], [c_42, c_905])).
% 4.20/1.88  tff(c_362, plain, (![A_223, B_224, C_225, D_226]: (k8_relset_1(A_223, B_224, C_225, D_226)=k10_relat_1(C_225, D_226) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.20/1.88  tff(c_369, plain, (![D_226]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_226)=k10_relat_1('#skF_9', D_226))), inference(resolution, [status(thm)], [c_42, c_362])).
% 4.20/1.88  tff(c_64, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/1.88  tff(c_71, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_64])).
% 4.20/1.88  tff(c_56, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/1.88  tff(c_72, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_56])).
% 4.20/1.88  tff(c_60, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/1.88  tff(c_91, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_60])).
% 4.20/1.88  tff(c_214, plain, (![D_198, A_199, B_200, E_201]: (r2_hidden(D_198, k10_relat_1(A_199, B_200)) | ~r2_hidden(E_201, B_200) | ~r2_hidden(k4_tarski(D_198, E_201), A_199) | ~v1_relat_1(A_199))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.20/1.88  tff(c_233, plain, (![D_202, A_203]: (r2_hidden(D_202, k10_relat_1(A_203, '#skF_7')) | ~r2_hidden(k4_tarski(D_202, '#skF_11'), A_203) | ~v1_relat_1(A_203))), inference(resolution, [status(thm)], [c_72, c_214])).
% 4.20/1.88  tff(c_239, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_91, c_233])).
% 4.20/1.88  tff(c_243, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_239])).
% 4.20/1.88  tff(c_171, plain, (![A_184, B_185, C_186, D_187]: (k8_relset_1(A_184, B_185, C_186, D_187)=k10_relat_1(C_186, D_187) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.20/1.88  tff(c_182, plain, (![D_187]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_187)=k10_relat_1('#skF_9', D_187))), inference(resolution, [status(thm)], [c_42, c_171])).
% 4.20/1.88  tff(c_50, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/1.88  tff(c_291, plain, (![F_209]: (~r2_hidden(F_209, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_209), '#skF_9') | ~m1_subset_1(F_209, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_182, c_50])).
% 4.20/1.88  tff(c_302, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_91, c_291])).
% 4.20/1.88  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_72, c_302])).
% 4.20/1.88  tff(c_313, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_60])).
% 4.20/1.88  tff(c_372, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_313])).
% 4.20/1.88  tff(c_26, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_5'(A_49, B_50, C_51), B_50) | ~r2_hidden(A_49, k10_relat_1(C_51, B_50)) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.20/1.88  tff(c_433, plain, (![A_243, B_244, C_245]: (r2_hidden(k4_tarski(A_243, '#skF_5'(A_243, B_244, C_245)), C_245) | ~r2_hidden(A_243, k10_relat_1(C_245, B_244)) | ~v1_relat_1(C_245))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.20/1.88  tff(c_314, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_60])).
% 4.20/1.88  tff(c_58, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/1.88  tff(c_409, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_314, c_58])).
% 4.20/1.88  tff(c_437, plain, (![B_244]: (~r2_hidden('#skF_5'('#skF_10', B_244, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_244, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_244)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_433, c_409])).
% 4.20/1.88  tff(c_533, plain, (![B_263]: (~r2_hidden('#skF_5'('#skF_10', B_263, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_263, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_263)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_437])).
% 4.20/1.88  tff(c_541, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_533])).
% 4.20/1.88  tff(c_547, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_372, c_541])).
% 4.20/1.88  tff(c_82, plain, (![A_166, B_167, C_168]: (k2_relset_1(A_166, B_167, C_168)=k2_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.20/1.88  tff(c_86, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_82])).
% 4.20/1.88  tff(c_331, plain, (![A_214, B_215, C_216]: (m1_subset_1(k2_relset_1(A_214, B_215, C_216), k1_zfmisc_1(B_215)) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.20/1.88  tff(c_342, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_86, c_331])).
% 4.20/1.88  tff(c_346, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_342])).
% 4.20/1.88  tff(c_354, plain, (![A_220, B_221, C_222]: (r2_hidden('#skF_5'(A_220, B_221, C_222), k2_relat_1(C_222)) | ~r2_hidden(A_220, k10_relat_1(C_222, B_221)) | ~v1_relat_1(C_222))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.20/1.88  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.20/1.88  tff(c_708, plain, (![A_285, B_286, C_287, A_288]: (r2_hidden('#skF_5'(A_285, B_286, C_287), A_288) | ~m1_subset_1(k2_relat_1(C_287), k1_zfmisc_1(A_288)) | ~r2_hidden(A_285, k10_relat_1(C_287, B_286)) | ~v1_relat_1(C_287))), inference(resolution, [status(thm)], [c_354, c_2])).
% 4.20/1.88  tff(c_710, plain, (![A_285, B_286]: (r2_hidden('#skF_5'(A_285, B_286, '#skF_9'), '#skF_8') | ~r2_hidden(A_285, k10_relat_1('#skF_9', B_286)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_346, c_708])).
% 4.20/1.88  tff(c_731, plain, (![A_293, B_294]: (r2_hidden('#skF_5'(A_293, B_294, '#skF_9'), '#skF_8') | ~r2_hidden(A_293, k10_relat_1('#skF_9', B_294)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_710])).
% 4.20/1.88  tff(c_4, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.20/1.88  tff(c_742, plain, (![A_295, B_296]: (m1_subset_1('#skF_5'(A_295, B_296, '#skF_9'), '#skF_8') | ~r2_hidden(A_295, k10_relat_1('#skF_9', B_296)))), inference(resolution, [status(thm)], [c_731, c_4])).
% 4.20/1.88  tff(c_773, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_372, c_742])).
% 4.20/1.88  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_547, c_773])).
% 4.20/1.88  tff(c_791, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_56])).
% 4.20/1.88  tff(c_927, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_916, c_791])).
% 4.20/1.88  tff(c_969, plain, (![A_336, B_337, C_338]: (r2_hidden(k4_tarski(A_336, '#skF_5'(A_336, B_337, C_338)), C_338) | ~r2_hidden(A_336, k10_relat_1(C_338, B_337)) | ~v1_relat_1(C_338))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.20/1.88  tff(c_792, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 4.20/1.88  tff(c_54, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/1.88  tff(c_824, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_792, c_54])).
% 4.20/1.88  tff(c_978, plain, (![B_337]: (~r2_hidden('#skF_5'('#skF_10', B_337, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_337, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_337)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_969, c_824])).
% 4.20/1.88  tff(c_1134, plain, (![B_367]: (~r2_hidden('#skF_5'('#skF_10', B_367, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_367, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_367)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_978])).
% 4.20/1.88  tff(c_1142, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_1134])).
% 4.20/1.88  tff(c_1148, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_927, c_1142])).
% 4.20/1.88  tff(c_841, plain, (![A_306, B_307, C_308]: (k2_relset_1(A_306, B_307, C_308)=k2_relat_1(C_308) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.20/1.88  tff(c_850, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_841])).
% 4.20/1.88  tff(c_863, plain, (![A_312, B_313, C_314]: (m1_subset_1(k2_relset_1(A_312, B_313, C_314), k1_zfmisc_1(B_313)) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.20/1.88  tff(c_874, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_850, c_863])).
% 4.20/1.88  tff(c_878, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_874])).
% 4.20/1.88  tff(c_917, plain, (![A_324, B_325, C_326]: (r2_hidden('#skF_5'(A_324, B_325, C_326), k2_relat_1(C_326)) | ~r2_hidden(A_324, k10_relat_1(C_326, B_325)) | ~v1_relat_1(C_326))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.20/1.88  tff(c_1369, plain, (![A_397, B_398, C_399, A_400]: (r2_hidden('#skF_5'(A_397, B_398, C_399), A_400) | ~m1_subset_1(k2_relat_1(C_399), k1_zfmisc_1(A_400)) | ~r2_hidden(A_397, k10_relat_1(C_399, B_398)) | ~v1_relat_1(C_399))), inference(resolution, [status(thm)], [c_917, c_2])).
% 4.20/1.88  tff(c_1371, plain, (![A_397, B_398]: (r2_hidden('#skF_5'(A_397, B_398, '#skF_9'), '#skF_8') | ~r2_hidden(A_397, k10_relat_1('#skF_9', B_398)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_878, c_1369])).
% 4.20/1.88  tff(c_1375, plain, (![A_401, B_402]: (r2_hidden('#skF_5'(A_401, B_402, '#skF_9'), '#skF_8') | ~r2_hidden(A_401, k10_relat_1('#skF_9', B_402)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1371])).
% 4.20/1.88  tff(c_1386, plain, (![A_403, B_404]: (m1_subset_1('#skF_5'(A_403, B_404, '#skF_9'), '#skF_8') | ~r2_hidden(A_403, k10_relat_1('#skF_9', B_404)))), inference(resolution, [status(thm)], [c_1375, c_4])).
% 4.20/1.88  tff(c_1421, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_927, c_1386])).
% 4.20/1.88  tff(c_1443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1148, c_1421])).
% 4.20/1.88  tff(c_1444, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_64])).
% 4.20/1.88  tff(c_1513, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_1444])).
% 4.20/1.88  tff(c_1548, plain, (![A_432, B_433, C_434]: (r2_hidden(k4_tarski(A_432, '#skF_5'(A_432, B_433, C_434)), C_434) | ~r2_hidden(A_432, k10_relat_1(C_434, B_433)) | ~v1_relat_1(C_434))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.20/1.88  tff(c_1445, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_64])).
% 4.20/1.88  tff(c_62, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/1.88  tff(c_1536, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_156), '#skF_9') | ~m1_subset_1(F_156, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1445, c_62])).
% 4.20/1.88  tff(c_1552, plain, (![B_433]: (~r2_hidden('#skF_5'('#skF_10', B_433, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_433, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_433)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1548, c_1536])).
% 4.20/1.88  tff(c_1703, plain, (![B_468]: (~r2_hidden('#skF_5'('#skF_10', B_468, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_468, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_468)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1552])).
% 4.20/1.88  tff(c_1711, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_1703])).
% 4.20/1.88  tff(c_1717, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1513, c_1711])).
% 4.20/1.88  tff(c_1464, plain, (![A_410, B_411, C_412]: (k2_relset_1(A_410, B_411, C_412)=k2_relat_1(C_412) | ~m1_subset_1(C_412, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.20/1.88  tff(c_1468, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_1464])).
% 4.20/1.88  tff(c_1474, plain, (![A_413, B_414, C_415]: (m1_subset_1(k2_relset_1(A_413, B_414, C_415), k1_zfmisc_1(B_414)) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_413, B_414))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.20/1.88  tff(c_1485, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1468, c_1474])).
% 4.20/1.88  tff(c_1489, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1485])).
% 4.20/1.88  tff(c_1540, plain, (![A_429, B_430, C_431]: (r2_hidden('#skF_5'(A_429, B_430, C_431), k2_relat_1(C_431)) | ~r2_hidden(A_429, k10_relat_1(C_431, B_430)) | ~v1_relat_1(C_431))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.20/1.88  tff(c_1839, plain, (![A_486, B_487, C_488, A_489]: (r2_hidden('#skF_5'(A_486, B_487, C_488), A_489) | ~m1_subset_1(k2_relat_1(C_488), k1_zfmisc_1(A_489)) | ~r2_hidden(A_486, k10_relat_1(C_488, B_487)) | ~v1_relat_1(C_488))), inference(resolution, [status(thm)], [c_1540, c_2])).
% 4.20/1.88  tff(c_1841, plain, (![A_486, B_487]: (r2_hidden('#skF_5'(A_486, B_487, '#skF_9'), '#skF_8') | ~r2_hidden(A_486, k10_relat_1('#skF_9', B_487)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1489, c_1839])).
% 4.20/1.88  tff(c_1845, plain, (![A_490, B_491]: (r2_hidden('#skF_5'(A_490, B_491, '#skF_9'), '#skF_8') | ~r2_hidden(A_490, k10_relat_1('#skF_9', B_491)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1841])).
% 4.20/1.88  tff(c_1856, plain, (![A_492, B_493]: (m1_subset_1('#skF_5'(A_492, B_493, '#skF_9'), '#skF_8') | ~r2_hidden(A_492, k10_relat_1('#skF_9', B_493)))), inference(resolution, [status(thm)], [c_1845, c_4])).
% 4.20/1.88  tff(c_1887, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1513, c_1856])).
% 4.20/1.88  tff(c_1904, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1717, c_1887])).
% 4.20/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.88  
% 4.20/1.88  Inference rules
% 4.20/1.88  ----------------------
% 4.20/1.88  #Ref     : 0
% 4.20/1.88  #Sup     : 401
% 4.20/1.88  #Fact    : 0
% 4.20/1.88  #Define  : 0
% 4.20/1.88  #Split   : 16
% 4.20/1.88  #Chain   : 0
% 4.20/1.88  #Close   : 0
% 4.20/1.88  
% 4.20/1.88  Ordering : KBO
% 4.20/1.88  
% 4.20/1.88  Simplification rules
% 4.20/1.88  ----------------------
% 4.20/1.88  #Subsume      : 21
% 4.20/1.88  #Demod        : 74
% 4.20/1.88  #Tautology    : 24
% 4.20/1.88  #SimpNegUnit  : 6
% 4.20/1.88  #BackRed      : 9
% 4.20/1.88  
% 4.20/1.88  #Partial instantiations: 0
% 4.20/1.88  #Strategies tried      : 1
% 4.20/1.88  
% 4.20/1.88  Timing (in seconds)
% 4.20/1.88  ----------------------
% 4.20/1.88  Preprocessing        : 0.35
% 4.20/1.88  Parsing              : 0.17
% 4.20/1.88  CNF conversion       : 0.04
% 4.20/1.89  Main loop            : 0.62
% 4.20/1.89  Inferencing          : 0.24
% 4.20/1.89  Reduction            : 0.17
% 4.20/1.89  Demodulation         : 0.11
% 4.20/1.89  BG Simplification    : 0.03
% 4.20/1.89  Subsumption          : 0.13
% 4.20/1.89  Abstraction          : 0.04
% 4.20/1.89  MUC search           : 0.00
% 4.20/1.89  Cooper               : 0.00
% 4.20/1.89  Total                : 1.02
% 4.20/1.89  Index Insertion      : 0.00
% 4.20/1.89  Index Deletion       : 0.00
% 4.20/1.89  Index Matching       : 0.00
% 4.20/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
