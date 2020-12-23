%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:36 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.57s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 249 expanded)
%              Number of leaves         :   29 (  96 expanded)
%              Depth                    :    9
%              Number of atoms          :  204 ( 742 expanded)
%              Number of equality atoms :   10 (  31 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_90,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2493,plain,(
    ! [A_591,B_592,C_593,D_594] :
      ( k8_relset_1(A_591,B_592,C_593,D_594) = k10_relat_1(C_593,D_594)
      | ~ m1_subset_1(C_593,k1_zfmisc_1(k2_zfmisc_1(A_591,B_592))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2496,plain,(
    ! [D_594] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_594) = k10_relat_1('#skF_8',D_594) ),
    inference(resolution,[status(thm)],[c_36,c_2493])).

tff(c_1337,plain,(
    ! [A_397,B_398,C_399,D_400] :
      ( k8_relset_1(A_397,B_398,C_399,D_400) = k10_relat_1(C_399,D_400)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_397,B_398))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1340,plain,(
    ! [D_400] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_400) = k10_relat_1('#skF_8',D_400) ),
    inference(resolution,[status(thm)],[c_36,c_1337])).

tff(c_314,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( k8_relset_1(A_211,B_212,C_213,D_214) = k10_relat_1(C_213,D_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_317,plain,(
    ! [D_214] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_214) = k10_relat_1('#skF_8',D_214) ),
    inference(resolution,[status(thm)],[c_36,c_314])).

tff(c_58,plain,
    ( r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_66,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,
    ( r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6'))
    | r2_hidden('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_65,plain,(
    r2_hidden('#skF_10','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,
    ( r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_78,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    ! [C_151,A_152,B_153] :
      ( v1_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_60])).

tff(c_186,plain,(
    ! [D_191,A_192,B_193,E_194] :
      ( r2_hidden(D_191,k10_relat_1(A_192,B_193))
      | ~ r2_hidden(E_194,B_193)
      | ~ r2_hidden(k4_tarski(D_191,E_194),A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_205,plain,(
    ! [D_195,A_196] :
      ( r2_hidden(D_195,k10_relat_1(A_196,'#skF_6'))
      | ~ r2_hidden(k4_tarski(D_195,'#skF_10'),A_196)
      | ~ v1_relat_1(A_196) ) ),
    inference(resolution,[status(thm)],[c_65,c_186])).

tff(c_215,plain,
    ( r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_205])).

tff(c_220,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_215])).

tff(c_167,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( k8_relset_1(A_186,B_187,C_188,D_189) = k10_relat_1(C_188,D_189)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_174,plain,(
    ! [D_189] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_189) = k10_relat_1('#skF_8',D_189) ),
    inference(resolution,[status(thm)],[c_36,c_167])).

tff(c_44,plain,(
    ! [F_148] :
      ( ~ r2_hidden(F_148,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_148),'#skF_8')
      | ~ m1_subset_1(F_148,'#skF_7')
      | ~ r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_273,plain,(
    ! [F_205] :
      ( ~ r2_hidden(F_205,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_205),'#skF_8')
      | ~ m1_subset_1(F_205,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_174,c_44])).

tff(c_280,plain,
    ( ~ r2_hidden('#skF_10','#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_273])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65,c_280])).

tff(c_288,plain,(
    r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_320,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_288])).

tff(c_418,plain,(
    ! [D_249,A_250,B_251] :
      ( r2_hidden(k4_tarski(D_249,'#skF_4'(A_250,B_251,k10_relat_1(A_250,B_251),D_249)),A_250)
      | ~ r2_hidden(D_249,k10_relat_1(A_250,B_251))
      | ~ v1_relat_1(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_779,plain,(
    ! [D_310,A_311,B_312,A_313] :
      ( r2_hidden(k4_tarski(D_310,'#skF_4'(A_311,B_312,k10_relat_1(A_311,B_312),D_310)),A_313)
      | ~ m1_subset_1(A_311,k1_zfmisc_1(A_313))
      | ~ r2_hidden(D_310,k10_relat_1(A_311,B_312))
      | ~ v1_relat_1(A_311) ) ),
    inference(resolution,[status(thm)],[c_418,c_8])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1222,plain,(
    ! [C_368,B_370,A_366,D_367,D_369] :
      ( r2_hidden('#skF_4'(A_366,B_370,k10_relat_1(A_366,B_370),D_369),D_367)
      | ~ m1_subset_1(A_366,k1_zfmisc_1(k2_zfmisc_1(C_368,D_367)))
      | ~ r2_hidden(D_369,k10_relat_1(A_366,B_370))
      | ~ v1_relat_1(A_366) ) ),
    inference(resolution,[status(thm)],[c_779,c_4])).

tff(c_1251,plain,(
    ! [B_370,D_369] :
      ( r2_hidden('#skF_4'('#skF_8',B_370,k10_relat_1('#skF_8',B_370),D_369),'#skF_7')
      | ~ r2_hidden(D_369,k10_relat_1('#skF_8',B_370))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_1222])).

tff(c_1264,plain,(
    ! [B_371,D_372] :
      ( r2_hidden('#skF_4'('#skF_8',B_371,k10_relat_1('#skF_8',B_371),D_372),'#skF_7')
      | ~ r2_hidden(D_372,k10_relat_1('#skF_8',B_371)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1251])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1275,plain,(
    ! [B_373,D_374] :
      ( m1_subset_1('#skF_4'('#skF_8',B_373,k10_relat_1('#skF_8',B_373),D_374),'#skF_7')
      | ~ r2_hidden(D_374,k10_relat_1('#skF_8',B_373)) ) ),
    inference(resolution,[status(thm)],[c_1264,c_10])).

tff(c_14,plain,(
    ! [A_11,B_34,D_49] :
      ( r2_hidden('#skF_4'(A_11,B_34,k10_relat_1(A_11,B_34),D_49),B_34)
      | ~ r2_hidden(D_49,k10_relat_1(A_11,B_34))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_289,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [F_148] :
      ( ~ r2_hidden(F_148,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_148),'#skF_8')
      | ~ m1_subset_1(F_148,'#skF_7')
      | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_352,plain,(
    ! [F_148] :
      ( ~ r2_hidden(F_148,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_148),'#skF_8')
      | ~ m1_subset_1(F_148,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_52])).

tff(c_422,plain,(
    ! [B_251] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_251,k10_relat_1('#skF_8',B_251),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_251,k10_relat_1('#skF_8',B_251),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_251))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_418,c_352])).

tff(c_508,plain,(
    ! [B_262] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_262,k10_relat_1('#skF_8',B_262),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_262,k10_relat_1('#skF_8',B_262),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_262)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_422])).

tff(c_512,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_14,c_508])).

tff(c_515,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_320,c_512])).

tff(c_1286,plain,(
    ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1275,c_515])).

tff(c_1294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_1286])).

tff(c_1295,plain,(
    r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1343,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1340,c_1295])).

tff(c_1468,plain,(
    ! [D_436,A_437,B_438] :
      ( r2_hidden(k4_tarski(D_436,'#skF_4'(A_437,B_438,k10_relat_1(A_437,B_438),D_436)),A_437)
      | ~ r2_hidden(D_436,k10_relat_1(A_437,B_438))
      | ~ v1_relat_1(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1876,plain,(
    ! [D_503,A_504,B_505,A_506] :
      ( r2_hidden(k4_tarski(D_503,'#skF_4'(A_504,B_505,k10_relat_1(A_504,B_505),D_503)),A_506)
      | ~ m1_subset_1(A_504,k1_zfmisc_1(A_506))
      | ~ r2_hidden(D_503,k10_relat_1(A_504,B_505))
      | ~ v1_relat_1(A_504) ) ),
    inference(resolution,[status(thm)],[c_1468,c_8])).

tff(c_2372,plain,(
    ! [D_563,D_562,C_564,B_566,A_565] :
      ( r2_hidden('#skF_4'(A_565,B_566,k10_relat_1(A_565,B_566),D_562),D_563)
      | ~ m1_subset_1(A_565,k1_zfmisc_1(k2_zfmisc_1(C_564,D_563)))
      | ~ r2_hidden(D_562,k10_relat_1(A_565,B_566))
      | ~ v1_relat_1(A_565) ) ),
    inference(resolution,[status(thm)],[c_1876,c_4])).

tff(c_2413,plain,(
    ! [B_566,D_562] :
      ( r2_hidden('#skF_4'('#skF_8',B_566,k10_relat_1('#skF_8',B_566),D_562),'#skF_7')
      | ~ r2_hidden(D_562,k10_relat_1('#skF_8',B_566))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_2372])).

tff(c_2430,plain,(
    ! [B_567,D_568] :
      ( r2_hidden('#skF_4'('#skF_8',B_567,k10_relat_1('#skF_8',B_567),D_568),'#skF_7')
      | ~ r2_hidden(D_568,k10_relat_1('#skF_8',B_567)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2413])).

tff(c_2441,plain,(
    ! [B_569,D_570] :
      ( m1_subset_1('#skF_4'('#skF_8',B_569,k10_relat_1('#skF_8',B_569),D_570),'#skF_7')
      | ~ r2_hidden(D_570,k10_relat_1('#skF_8',B_569)) ) ),
    inference(resolution,[status(thm)],[c_2430,c_10])).

tff(c_1296,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [F_148] :
      ( ~ r2_hidden(F_148,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_148),'#skF_8')
      | ~ m1_subset_1(F_148,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1335,plain,(
    ! [F_148] :
      ( ~ r2_hidden(F_148,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_148),'#skF_8')
      | ~ m1_subset_1(F_148,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1296,c_56])).

tff(c_1474,plain,(
    ! [B_438] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_438,k10_relat_1('#skF_8',B_438),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_438,k10_relat_1('#skF_8',B_438),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_438))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1468,c_1335])).

tff(c_1496,plain,(
    ! [B_439] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_439,k10_relat_1('#skF_8',B_439),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_439,k10_relat_1('#skF_8',B_439),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_439)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1474])).

tff(c_1500,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_14,c_1496])).

tff(c_1503,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1343,c_1500])).

tff(c_2452,plain,(
    ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2441,c_1503])).

tff(c_2460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1343,c_2452])).

tff(c_2461,plain,(
    r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2499,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_2461])).

tff(c_2582,plain,(
    ! [D_620,A_621,B_622] :
      ( r2_hidden(k4_tarski(D_620,'#skF_4'(A_621,B_622,k10_relat_1(A_621,B_622),D_620)),A_621)
      | ~ r2_hidden(D_620,k10_relat_1(A_621,B_622))
      | ~ v1_relat_1(A_621) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2860,plain,(
    ! [D_672,A_673,B_674,A_675] :
      ( r2_hidden(k4_tarski(D_672,'#skF_4'(A_673,B_674,k10_relat_1(A_673,B_674),D_672)),A_675)
      | ~ m1_subset_1(A_673,k1_zfmisc_1(A_675))
      | ~ r2_hidden(D_672,k10_relat_1(A_673,B_674))
      | ~ v1_relat_1(A_673) ) ),
    inference(resolution,[status(thm)],[c_2582,c_8])).

tff(c_3326,plain,(
    ! [C_737,D_734,B_733,A_735,D_736] :
      ( r2_hidden('#skF_4'(A_735,B_733,k10_relat_1(A_735,B_733),D_736),D_734)
      | ~ m1_subset_1(A_735,k1_zfmisc_1(k2_zfmisc_1(C_737,D_734)))
      | ~ r2_hidden(D_736,k10_relat_1(A_735,B_733))
      | ~ v1_relat_1(A_735) ) ),
    inference(resolution,[status(thm)],[c_2860,c_4])).

tff(c_3358,plain,(
    ! [B_733,D_736] :
      ( r2_hidden('#skF_4'('#skF_8',B_733,k10_relat_1('#skF_8',B_733),D_736),'#skF_7')
      | ~ r2_hidden(D_736,k10_relat_1('#skF_8',B_733))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_3326])).

tff(c_3394,plain,(
    ! [B_741,D_742] :
      ( r2_hidden('#skF_4'('#skF_8',B_741,k10_relat_1('#skF_8',B_741),D_742),'#skF_7')
      | ~ r2_hidden(D_742,k10_relat_1('#skF_8',B_741)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3358])).

tff(c_3405,plain,(
    ! [B_743,D_744] :
      ( m1_subset_1('#skF_4'('#skF_8',B_743,k10_relat_1('#skF_8',B_743),D_744),'#skF_7')
      | ~ r2_hidden(D_744,k10_relat_1('#skF_8',B_743)) ) ),
    inference(resolution,[status(thm)],[c_3394,c_10])).

tff(c_2462,plain,(
    ~ r2_hidden('#skF_10','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [F_148] :
      ( ~ r2_hidden(F_148,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_148),'#skF_8')
      | ~ m1_subset_1(F_148,'#skF_7')
      | r2_hidden('#skF_10','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2509,plain,(
    ! [F_148] :
      ( ~ r2_hidden(F_148,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_148),'#skF_8')
      | ~ m1_subset_1(F_148,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2462,c_48])).

tff(c_2588,plain,(
    ! [B_622] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_622,k10_relat_1('#skF_8',B_622),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_622,k10_relat_1('#skF_8',B_622),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_622))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2582,c_2509])).

tff(c_2729,plain,(
    ! [B_649] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_649,k10_relat_1('#skF_8',B_649),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_649,k10_relat_1('#skF_8',B_649),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_649)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2588])).

tff(c_2733,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_14,c_2729])).

tff(c_2736,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2499,c_2733])).

tff(c_3416,plain,(
    ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_3405,c_2736])).

tff(c_3424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2499,c_3416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:08:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.52/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.07  
% 5.52/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.07  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 5.57/2.07  
% 5.57/2.07  %Foreground sorts:
% 5.57/2.07  
% 5.57/2.07  
% 5.57/2.07  %Background operators:
% 5.57/2.07  
% 5.57/2.07  
% 5.57/2.07  %Foreground operators:
% 5.57/2.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.57/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.57/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.57/2.07  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.57/2.07  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.57/2.07  tff('#skF_7', type, '#skF_7': $i).
% 5.57/2.07  tff('#skF_10', type, '#skF_10': $i).
% 5.57/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.57/2.07  tff('#skF_6', type, '#skF_6': $i).
% 5.57/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.57/2.07  tff('#skF_9', type, '#skF_9': $i).
% 5.57/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.57/2.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.57/2.07  tff('#skF_8', type, '#skF_8': $i).
% 5.57/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.57/2.07  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.57/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.57/2.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.57/2.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.57/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.57/2.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.57/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.57/2.07  
% 5.57/2.09  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 5.57/2.09  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.57/2.09  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.57/2.09  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 5.57/2.09  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.57/2.09  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 5.57/2.09  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.57/2.09  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.57/2.09  tff(c_2493, plain, (![A_591, B_592, C_593, D_594]: (k8_relset_1(A_591, B_592, C_593, D_594)=k10_relat_1(C_593, D_594) | ~m1_subset_1(C_593, k1_zfmisc_1(k2_zfmisc_1(A_591, B_592))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.57/2.09  tff(c_2496, plain, (![D_594]: (k8_relset_1('#skF_5', '#skF_7', '#skF_8', D_594)=k10_relat_1('#skF_8', D_594))), inference(resolution, [status(thm)], [c_36, c_2493])).
% 5.57/2.09  tff(c_1337, plain, (![A_397, B_398, C_399, D_400]: (k8_relset_1(A_397, B_398, C_399, D_400)=k10_relat_1(C_399, D_400) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_397, B_398))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.57/2.09  tff(c_1340, plain, (![D_400]: (k8_relset_1('#skF_5', '#skF_7', '#skF_8', D_400)=k10_relat_1('#skF_8', D_400))), inference(resolution, [status(thm)], [c_36, c_1337])).
% 5.57/2.09  tff(c_314, plain, (![A_211, B_212, C_213, D_214]: (k8_relset_1(A_211, B_212, C_213, D_214)=k10_relat_1(C_213, D_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.57/2.09  tff(c_317, plain, (![D_214]: (k8_relset_1('#skF_5', '#skF_7', '#skF_8', D_214)=k10_relat_1('#skF_8', D_214))), inference(resolution, [status(thm)], [c_36, c_314])).
% 5.57/2.09  tff(c_58, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6')) | m1_subset_1('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.57/2.09  tff(c_66, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_58])).
% 5.57/2.09  tff(c_50, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6')) | r2_hidden('#skF_10', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.57/2.09  tff(c_65, plain, (r2_hidden('#skF_10', '#skF_6')), inference(splitLeft, [status(thm)], [c_50])).
% 5.57/2.09  tff(c_54, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.57/2.09  tff(c_78, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_54])).
% 5.57/2.09  tff(c_60, plain, (![C_151, A_152, B_153]: (v1_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.57/2.09  tff(c_64, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_60])).
% 5.57/2.09  tff(c_186, plain, (![D_191, A_192, B_193, E_194]: (r2_hidden(D_191, k10_relat_1(A_192, B_193)) | ~r2_hidden(E_194, B_193) | ~r2_hidden(k4_tarski(D_191, E_194), A_192) | ~v1_relat_1(A_192))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.57/2.09  tff(c_205, plain, (![D_195, A_196]: (r2_hidden(D_195, k10_relat_1(A_196, '#skF_6')) | ~r2_hidden(k4_tarski(D_195, '#skF_10'), A_196) | ~v1_relat_1(A_196))), inference(resolution, [status(thm)], [c_65, c_186])).
% 5.57/2.09  tff(c_215, plain, (r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_78, c_205])).
% 5.57/2.09  tff(c_220, plain, (r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_215])).
% 5.57/2.09  tff(c_167, plain, (![A_186, B_187, C_188, D_189]: (k8_relset_1(A_186, B_187, C_188, D_189)=k10_relat_1(C_188, D_189) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.57/2.09  tff(c_174, plain, (![D_189]: (k8_relset_1('#skF_5', '#skF_7', '#skF_8', D_189)=k10_relat_1('#skF_8', D_189))), inference(resolution, [status(thm)], [c_36, c_167])).
% 5.57/2.09  tff(c_44, plain, (![F_148]: (~r2_hidden(F_148, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_148), '#skF_8') | ~m1_subset_1(F_148, '#skF_7') | ~r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.57/2.09  tff(c_273, plain, (![F_205]: (~r2_hidden(F_205, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_205), '#skF_8') | ~m1_subset_1(F_205, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_174, c_44])).
% 5.57/2.09  tff(c_280, plain, (~r2_hidden('#skF_10', '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_78, c_273])).
% 5.57/2.09  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_65, c_280])).
% 5.57/2.09  tff(c_288, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6'))), inference(splitRight, [status(thm)], [c_54])).
% 5.57/2.09  tff(c_320, plain, (r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_288])).
% 5.57/2.09  tff(c_418, plain, (![D_249, A_250, B_251]: (r2_hidden(k4_tarski(D_249, '#skF_4'(A_250, B_251, k10_relat_1(A_250, B_251), D_249)), A_250) | ~r2_hidden(D_249, k10_relat_1(A_250, B_251)) | ~v1_relat_1(A_250))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.57/2.09  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.57/2.09  tff(c_779, plain, (![D_310, A_311, B_312, A_313]: (r2_hidden(k4_tarski(D_310, '#skF_4'(A_311, B_312, k10_relat_1(A_311, B_312), D_310)), A_313) | ~m1_subset_1(A_311, k1_zfmisc_1(A_313)) | ~r2_hidden(D_310, k10_relat_1(A_311, B_312)) | ~v1_relat_1(A_311))), inference(resolution, [status(thm)], [c_418, c_8])).
% 5.57/2.09  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.57/2.09  tff(c_1222, plain, (![C_368, B_370, A_366, D_367, D_369]: (r2_hidden('#skF_4'(A_366, B_370, k10_relat_1(A_366, B_370), D_369), D_367) | ~m1_subset_1(A_366, k1_zfmisc_1(k2_zfmisc_1(C_368, D_367))) | ~r2_hidden(D_369, k10_relat_1(A_366, B_370)) | ~v1_relat_1(A_366))), inference(resolution, [status(thm)], [c_779, c_4])).
% 5.57/2.09  tff(c_1251, plain, (![B_370, D_369]: (r2_hidden('#skF_4'('#skF_8', B_370, k10_relat_1('#skF_8', B_370), D_369), '#skF_7') | ~r2_hidden(D_369, k10_relat_1('#skF_8', B_370)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_36, c_1222])).
% 5.57/2.09  tff(c_1264, plain, (![B_371, D_372]: (r2_hidden('#skF_4'('#skF_8', B_371, k10_relat_1('#skF_8', B_371), D_372), '#skF_7') | ~r2_hidden(D_372, k10_relat_1('#skF_8', B_371)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1251])).
% 5.57/2.09  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.57/2.09  tff(c_1275, plain, (![B_373, D_374]: (m1_subset_1('#skF_4'('#skF_8', B_373, k10_relat_1('#skF_8', B_373), D_374), '#skF_7') | ~r2_hidden(D_374, k10_relat_1('#skF_8', B_373)))), inference(resolution, [status(thm)], [c_1264, c_10])).
% 5.57/2.09  tff(c_14, plain, (![A_11, B_34, D_49]: (r2_hidden('#skF_4'(A_11, B_34, k10_relat_1(A_11, B_34), D_49), B_34) | ~r2_hidden(D_49, k10_relat_1(A_11, B_34)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.57/2.09  tff(c_289, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_54])).
% 5.57/2.09  tff(c_52, plain, (![F_148]: (~r2_hidden(F_148, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_148), '#skF_8') | ~m1_subset_1(F_148, '#skF_7') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.57/2.09  tff(c_352, plain, (![F_148]: (~r2_hidden(F_148, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_148), '#skF_8') | ~m1_subset_1(F_148, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_289, c_52])).
% 5.57/2.09  tff(c_422, plain, (![B_251]: (~r2_hidden('#skF_4'('#skF_8', B_251, k10_relat_1('#skF_8', B_251), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_251, k10_relat_1('#skF_8', B_251), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_251)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_418, c_352])).
% 5.57/2.09  tff(c_508, plain, (![B_262]: (~r2_hidden('#skF_4'('#skF_8', B_262, k10_relat_1('#skF_8', B_262), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_262, k10_relat_1('#skF_8', B_262), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_262)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_422])).
% 5.57/2.09  tff(c_512, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_14, c_508])).
% 5.57/2.09  tff(c_515, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_320, c_512])).
% 5.57/2.09  tff(c_1286, plain, (~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_1275, c_515])).
% 5.57/2.09  tff(c_1294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_320, c_1286])).
% 5.57/2.09  tff(c_1295, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6'))), inference(splitRight, [status(thm)], [c_58])).
% 5.57/2.09  tff(c_1343, plain, (r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1340, c_1295])).
% 5.57/2.09  tff(c_1468, plain, (![D_436, A_437, B_438]: (r2_hidden(k4_tarski(D_436, '#skF_4'(A_437, B_438, k10_relat_1(A_437, B_438), D_436)), A_437) | ~r2_hidden(D_436, k10_relat_1(A_437, B_438)) | ~v1_relat_1(A_437))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.57/2.09  tff(c_1876, plain, (![D_503, A_504, B_505, A_506]: (r2_hidden(k4_tarski(D_503, '#skF_4'(A_504, B_505, k10_relat_1(A_504, B_505), D_503)), A_506) | ~m1_subset_1(A_504, k1_zfmisc_1(A_506)) | ~r2_hidden(D_503, k10_relat_1(A_504, B_505)) | ~v1_relat_1(A_504))), inference(resolution, [status(thm)], [c_1468, c_8])).
% 5.57/2.09  tff(c_2372, plain, (![D_563, D_562, C_564, B_566, A_565]: (r2_hidden('#skF_4'(A_565, B_566, k10_relat_1(A_565, B_566), D_562), D_563) | ~m1_subset_1(A_565, k1_zfmisc_1(k2_zfmisc_1(C_564, D_563))) | ~r2_hidden(D_562, k10_relat_1(A_565, B_566)) | ~v1_relat_1(A_565))), inference(resolution, [status(thm)], [c_1876, c_4])).
% 5.57/2.09  tff(c_2413, plain, (![B_566, D_562]: (r2_hidden('#skF_4'('#skF_8', B_566, k10_relat_1('#skF_8', B_566), D_562), '#skF_7') | ~r2_hidden(D_562, k10_relat_1('#skF_8', B_566)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_36, c_2372])).
% 5.57/2.09  tff(c_2430, plain, (![B_567, D_568]: (r2_hidden('#skF_4'('#skF_8', B_567, k10_relat_1('#skF_8', B_567), D_568), '#skF_7') | ~r2_hidden(D_568, k10_relat_1('#skF_8', B_567)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2413])).
% 5.57/2.09  tff(c_2441, plain, (![B_569, D_570]: (m1_subset_1('#skF_4'('#skF_8', B_569, k10_relat_1('#skF_8', B_569), D_570), '#skF_7') | ~r2_hidden(D_570, k10_relat_1('#skF_8', B_569)))), inference(resolution, [status(thm)], [c_2430, c_10])).
% 5.57/2.09  tff(c_1296, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_58])).
% 5.57/2.09  tff(c_56, plain, (![F_148]: (~r2_hidden(F_148, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_148), '#skF_8') | ~m1_subset_1(F_148, '#skF_7') | m1_subset_1('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.57/2.09  tff(c_1335, plain, (![F_148]: (~r2_hidden(F_148, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_148), '#skF_8') | ~m1_subset_1(F_148, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_1296, c_56])).
% 5.57/2.09  tff(c_1474, plain, (![B_438]: (~r2_hidden('#skF_4'('#skF_8', B_438, k10_relat_1('#skF_8', B_438), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_438, k10_relat_1('#skF_8', B_438), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_438)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1468, c_1335])).
% 5.57/2.09  tff(c_1496, plain, (![B_439]: (~r2_hidden('#skF_4'('#skF_8', B_439, k10_relat_1('#skF_8', B_439), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_439, k10_relat_1('#skF_8', B_439), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_439)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1474])).
% 5.57/2.09  tff(c_1500, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_14, c_1496])).
% 5.57/2.09  tff(c_1503, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1343, c_1500])).
% 5.57/2.09  tff(c_2452, plain, (~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_2441, c_1503])).
% 5.57/2.09  tff(c_2460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1343, c_2452])).
% 5.57/2.09  tff(c_2461, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6'))), inference(splitRight, [status(thm)], [c_50])).
% 5.57/2.09  tff(c_2499, plain, (r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_2461])).
% 5.57/2.09  tff(c_2582, plain, (![D_620, A_621, B_622]: (r2_hidden(k4_tarski(D_620, '#skF_4'(A_621, B_622, k10_relat_1(A_621, B_622), D_620)), A_621) | ~r2_hidden(D_620, k10_relat_1(A_621, B_622)) | ~v1_relat_1(A_621))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.57/2.09  tff(c_2860, plain, (![D_672, A_673, B_674, A_675]: (r2_hidden(k4_tarski(D_672, '#skF_4'(A_673, B_674, k10_relat_1(A_673, B_674), D_672)), A_675) | ~m1_subset_1(A_673, k1_zfmisc_1(A_675)) | ~r2_hidden(D_672, k10_relat_1(A_673, B_674)) | ~v1_relat_1(A_673))), inference(resolution, [status(thm)], [c_2582, c_8])).
% 5.57/2.09  tff(c_3326, plain, (![C_737, D_734, B_733, A_735, D_736]: (r2_hidden('#skF_4'(A_735, B_733, k10_relat_1(A_735, B_733), D_736), D_734) | ~m1_subset_1(A_735, k1_zfmisc_1(k2_zfmisc_1(C_737, D_734))) | ~r2_hidden(D_736, k10_relat_1(A_735, B_733)) | ~v1_relat_1(A_735))), inference(resolution, [status(thm)], [c_2860, c_4])).
% 5.57/2.09  tff(c_3358, plain, (![B_733, D_736]: (r2_hidden('#skF_4'('#skF_8', B_733, k10_relat_1('#skF_8', B_733), D_736), '#skF_7') | ~r2_hidden(D_736, k10_relat_1('#skF_8', B_733)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_36, c_3326])).
% 5.57/2.09  tff(c_3394, plain, (![B_741, D_742]: (r2_hidden('#skF_4'('#skF_8', B_741, k10_relat_1('#skF_8', B_741), D_742), '#skF_7') | ~r2_hidden(D_742, k10_relat_1('#skF_8', B_741)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3358])).
% 5.57/2.09  tff(c_3405, plain, (![B_743, D_744]: (m1_subset_1('#skF_4'('#skF_8', B_743, k10_relat_1('#skF_8', B_743), D_744), '#skF_7') | ~r2_hidden(D_744, k10_relat_1('#skF_8', B_743)))), inference(resolution, [status(thm)], [c_3394, c_10])).
% 5.57/2.09  tff(c_2462, plain, (~r2_hidden('#skF_10', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 5.57/2.09  tff(c_48, plain, (![F_148]: (~r2_hidden(F_148, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_148), '#skF_8') | ~m1_subset_1(F_148, '#skF_7') | r2_hidden('#skF_10', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.57/2.09  tff(c_2509, plain, (![F_148]: (~r2_hidden(F_148, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_148), '#skF_8') | ~m1_subset_1(F_148, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_2462, c_48])).
% 5.57/2.09  tff(c_2588, plain, (![B_622]: (~r2_hidden('#skF_4'('#skF_8', B_622, k10_relat_1('#skF_8', B_622), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_622, k10_relat_1('#skF_8', B_622), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_622)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_2582, c_2509])).
% 5.57/2.09  tff(c_2729, plain, (![B_649]: (~r2_hidden('#skF_4'('#skF_8', B_649, k10_relat_1('#skF_8', B_649), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_649, k10_relat_1('#skF_8', B_649), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_649)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2588])).
% 5.57/2.09  tff(c_2733, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_14, c_2729])).
% 5.57/2.09  tff(c_2736, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2499, c_2733])).
% 5.57/2.09  tff(c_3416, plain, (~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_3405, c_2736])).
% 5.57/2.09  tff(c_3424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2499, c_3416])).
% 5.57/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.09  
% 5.57/2.09  Inference rules
% 5.57/2.09  ----------------------
% 5.57/2.09  #Ref     : 0
% 5.57/2.09  #Sup     : 743
% 5.57/2.09  #Fact    : 0
% 5.57/2.09  #Define  : 0
% 5.57/2.09  #Split   : 11
% 5.57/2.09  #Chain   : 0
% 5.57/2.09  #Close   : 0
% 5.57/2.09  
% 5.57/2.09  Ordering : KBO
% 5.57/2.09  
% 5.57/2.09  Simplification rules
% 5.57/2.09  ----------------------
% 5.57/2.09  #Subsume      : 26
% 5.57/2.09  #Demod        : 85
% 5.57/2.09  #Tautology    : 39
% 5.57/2.09  #SimpNegUnit  : 3
% 5.57/2.09  #BackRed      : 9
% 5.57/2.09  
% 5.57/2.09  #Partial instantiations: 0
% 5.57/2.09  #Strategies tried      : 1
% 5.57/2.09  
% 5.57/2.09  Timing (in seconds)
% 5.57/2.09  ----------------------
% 5.57/2.10  Preprocessing        : 0.35
% 5.57/2.10  Parsing              : 0.18
% 5.57/2.10  CNF conversion       : 0.03
% 5.57/2.10  Main loop            : 0.93
% 5.57/2.10  Inferencing          : 0.36
% 5.57/2.10  Reduction            : 0.24
% 5.57/2.10  Demodulation         : 0.16
% 5.57/2.10  BG Simplification    : 0.05
% 5.57/2.10  Subsumption          : 0.20
% 5.57/2.10  Abstraction          : 0.06
% 5.57/2.10  MUC search           : 0.00
% 5.57/2.10  Cooper               : 0.00
% 5.57/2.10  Total                : 1.32
% 5.57/2.10  Index Insertion      : 0.00
% 5.57/2.10  Index Deletion       : 0.00
% 5.57/2.10  Index Matching       : 0.00
% 5.57/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
