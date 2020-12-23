%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:38 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 298 expanded)
%              Number of leaves         :   30 ( 112 expanded)
%              Depth                    :    9
%              Number of atoms          :  218 ( 858 expanded)
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

tff(f_95,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3634,plain,(
    ! [A_714,B_715,C_716,D_717] :
      ( k8_relset_1(A_714,B_715,C_716,D_717) = k10_relat_1(C_716,D_717)
      | ~ m1_subset_1(C_716,k1_zfmisc_1(k2_zfmisc_1(A_714,B_715))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3637,plain,(
    ! [D_717] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_717) = k10_relat_1('#skF_8',D_717) ),
    inference(resolution,[status(thm)],[c_38,c_3634])).

tff(c_2368,plain,(
    ! [A_498,B_499,C_500,D_501] :
      ( k8_relset_1(A_498,B_499,C_500,D_501) = k10_relat_1(C_500,D_501)
      | ~ m1_subset_1(C_500,k1_zfmisc_1(k2_zfmisc_1(A_498,B_499))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2371,plain,(
    ! [D_501] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_501) = k10_relat_1('#skF_8',D_501) ),
    inference(resolution,[status(thm)],[c_38,c_2368])).

tff(c_305,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( k8_relset_1(A_211,B_212,C_213,D_214) = k10_relat_1(C_213,D_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_308,plain,(
    ! [D_214] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_214) = k10_relat_1('#skF_8',D_214) ),
    inference(resolution,[status(thm)],[c_38,c_305])).

tff(c_60,plain,
    ( r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_81,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_52,plain,
    ( r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6'))
    | r2_hidden('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_70,plain,(
    r2_hidden('#skF_10','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,
    ( r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_83,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_32,plain,(
    ! [A_56,B_57] : v1_relat_1(k2_zfmisc_1(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_63,plain,(
    ! [B_155,A_156] :
      ( v1_relat_1(B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_156))
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_38,c_63])).

tff(c_69,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_66])).

tff(c_191,plain,(
    ! [D_193,A_194,B_195,E_196] :
      ( r2_hidden(D_193,k10_relat_1(A_194,B_195))
      | ~ r2_hidden(E_196,B_195)
      | ~ r2_hidden(k4_tarski(D_193,E_196),A_194)
      | ~ v1_relat_1(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_210,plain,(
    ! [D_197,A_198] :
      ( r2_hidden(D_197,k10_relat_1(A_198,'#skF_6'))
      | ~ r2_hidden(k4_tarski(D_197,'#skF_10'),A_198)
      | ~ v1_relat_1(A_198) ) ),
    inference(resolution,[status(thm)],[c_70,c_191])).

tff(c_220,plain,
    ( r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_83,c_210])).

tff(c_227,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_220])).

tff(c_164,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( k8_relset_1(A_186,B_187,C_188,D_189) = k10_relat_1(C_188,D_189)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_171,plain,(
    ! [D_189] : k8_relset_1('#skF_5','#skF_7','#skF_8',D_189) = k10_relat_1('#skF_8',D_189) ),
    inference(resolution,[status(thm)],[c_38,c_164])).

tff(c_46,plain,(
    ! [F_150] :
      ( ~ r2_hidden(F_150,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_150),'#skF_8')
      | ~ m1_subset_1(F_150,'#skF_7')
      | ~ r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_264,plain,(
    ! [F_205] :
      ( ~ r2_hidden(F_205,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_205),'#skF_8')
      | ~ m1_subset_1(F_205,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_171,c_46])).

tff(c_271,plain,
    ( ~ r2_hidden('#skF_10','#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_83,c_264])).

tff(c_278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_70,c_271])).

tff(c_279,plain,(
    r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_311,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_279])).

tff(c_411,plain,(
    ! [D_249,A_250,B_251] :
      ( r2_hidden(k4_tarski(D_249,'#skF_4'(A_250,B_251,k10_relat_1(A_250,B_251),D_249)),A_250)
      | ~ r2_hidden(D_249,k10_relat_1(A_250,B_251))
      | ~ v1_relat_1(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1125,plain,(
    ! [D_369,A_370,B_371,A_372] :
      ( r2_hidden(k4_tarski(D_369,'#skF_4'(A_370,B_371,k10_relat_1(A_370,B_371),D_369)),A_372)
      | ~ m1_subset_1(A_370,k1_zfmisc_1(A_372))
      | ~ r2_hidden(D_369,k10_relat_1(A_370,B_371))
      | ~ v1_relat_1(A_370) ) ),
    inference(resolution,[status(thm)],[c_411,c_8])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2161,plain,(
    ! [B_473,D_471,A_475,C_474,D_472] :
      ( r2_hidden('#skF_4'(A_475,B_473,k10_relat_1(A_475,B_473),D_472),D_471)
      | ~ m1_subset_1(A_475,k1_zfmisc_1(k2_zfmisc_1(C_474,D_471)))
      | ~ r2_hidden(D_472,k10_relat_1(A_475,B_473))
      | ~ v1_relat_1(A_475) ) ),
    inference(resolution,[status(thm)],[c_1125,c_4])).

tff(c_2217,plain,(
    ! [B_473,D_472] :
      ( r2_hidden('#skF_4'('#skF_8',B_473,k10_relat_1('#skF_8',B_473),D_472),'#skF_7')
      | ~ r2_hidden(D_472,k10_relat_1('#skF_8',B_473))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_2161])).

tff(c_2239,plain,(
    ! [B_476,D_477] :
      ( r2_hidden('#skF_4'('#skF_8',B_476,k10_relat_1('#skF_8',B_476),D_477),'#skF_7')
      | ~ r2_hidden(D_477,k10_relat_1('#skF_8',B_476)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2217])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2250,plain,(
    ! [B_478,D_479] :
      ( m1_subset_1('#skF_4'('#skF_8',B_478,k10_relat_1('#skF_8',B_478),D_479),'#skF_7')
      | ~ r2_hidden(D_479,k10_relat_1('#skF_8',B_478)) ) ),
    inference(resolution,[status(thm)],[c_2239,c_10])).

tff(c_16,plain,(
    ! [A_14,B_37,D_52] :
      ( r2_hidden('#skF_4'(A_14,B_37,k10_relat_1(A_14,B_37),D_52),B_37)
      | ~ r2_hidden(D_52,k10_relat_1(A_14,B_37))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_280,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [F_150] :
      ( ~ r2_hidden(F_150,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_150),'#skF_8')
      | ~ m1_subset_1(F_150,'#skF_7')
      | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_343,plain,(
    ! [F_150] :
      ( ~ r2_hidden(F_150,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_150),'#skF_8')
      | ~ m1_subset_1(F_150,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_54])).

tff(c_415,plain,(
    ! [B_251] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_251,k10_relat_1('#skF_8',B_251),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_251,k10_relat_1('#skF_8',B_251),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_251))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_411,c_343])).

tff(c_477,plain,(
    ! [B_263] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_263,k10_relat_1('#skF_8',B_263),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_263,k10_relat_1('#skF_8',B_263),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_263)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_415])).

tff(c_481,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_477])).

tff(c_484,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_311,c_481])).

tff(c_2261,plain,(
    ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2250,c_484])).

tff(c_2269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_2261])).

tff(c_2271,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2272,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_2304,plain,(
    ! [A_485] :
      ( r2_hidden(k4_tarski('#skF_9','#skF_10'),A_485)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_485)) ) ),
    inference(resolution,[status(thm)],[c_2272,c_8])).

tff(c_2322,plain,(
    ! [D_486,C_487] :
      ( r2_hidden('#skF_10',D_486)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(C_487,D_486))) ) ),
    inference(resolution,[status(thm)],[c_2304,c_4])).

tff(c_2326,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_2322])).

tff(c_2332,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_2326,c_10])).

tff(c_2337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2271,c_2332])).

tff(c_2338,plain,(
    r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2374,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_2338])).

tff(c_2505,plain,(
    ! [D_542,A_543,B_544] :
      ( r2_hidden(k4_tarski(D_542,'#skF_4'(A_543,B_544,k10_relat_1(A_543,B_544),D_542)),A_543)
      | ~ r2_hidden(D_542,k10_relat_1(A_543,B_544))
      | ~ v1_relat_1(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2899,plain,(
    ! [D_606,A_607,B_608,A_609] :
      ( r2_hidden(k4_tarski(D_606,'#skF_4'(A_607,B_608,k10_relat_1(A_607,B_608),D_606)),A_609)
      | ~ m1_subset_1(A_607,k1_zfmisc_1(A_609))
      | ~ r2_hidden(D_606,k10_relat_1(A_607,B_608))
      | ~ v1_relat_1(A_607) ) ),
    inference(resolution,[status(thm)],[c_2505,c_8])).

tff(c_3525,plain,(
    ! [D_687,A_685,B_688,C_689,D_686] :
      ( r2_hidden('#skF_4'(A_685,B_688,k10_relat_1(A_685,B_688),D_687),D_686)
      | ~ m1_subset_1(A_685,k1_zfmisc_1(k2_zfmisc_1(C_689,D_686)))
      | ~ r2_hidden(D_687,k10_relat_1(A_685,B_688))
      | ~ v1_relat_1(A_685) ) ),
    inference(resolution,[status(thm)],[c_2899,c_4])).

tff(c_3557,plain,(
    ! [B_688,D_687] :
      ( r2_hidden('#skF_4'('#skF_8',B_688,k10_relat_1('#skF_8',B_688),D_687),'#skF_7')
      | ~ r2_hidden(D_687,k10_relat_1('#skF_8',B_688))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_3525])).

tff(c_3571,plain,(
    ! [B_690,D_691] :
      ( r2_hidden('#skF_4'('#skF_8',B_690,k10_relat_1('#skF_8',B_690),D_691),'#skF_7')
      | ~ r2_hidden(D_691,k10_relat_1('#skF_8',B_690)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_3557])).

tff(c_3582,plain,(
    ! [B_692,D_693] :
      ( m1_subset_1('#skF_4'('#skF_8',B_692,k10_relat_1('#skF_8',B_692),D_693),'#skF_7')
      | ~ r2_hidden(D_693,k10_relat_1('#skF_8',B_692)) ) ),
    inference(resolution,[status(thm)],[c_3571,c_10])).

tff(c_58,plain,(
    ! [F_150] :
      ( ~ r2_hidden(F_150,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_150),'#skF_8')
      | ~ m1_subset_1(F_150,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2392,plain,(
    ! [F_150] :
      ( ~ r2_hidden(F_150,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_150),'#skF_8')
      | ~ m1_subset_1(F_150,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2271,c_58])).

tff(c_2511,plain,(
    ! [B_544] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_544,k10_relat_1('#skF_8',B_544),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_544,k10_relat_1('#skF_8',B_544),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_544))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2505,c_2392])).

tff(c_2657,plain,(
    ! [B_565] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_565,k10_relat_1('#skF_8',B_565),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_565,k10_relat_1('#skF_8',B_565),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_565)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2511])).

tff(c_2661,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_2657])).

tff(c_2664,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_2374,c_2661])).

tff(c_3593,plain,(
    ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_3582,c_2664])).

tff(c_3601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2374,c_3593])).

tff(c_3602,plain,(
    r2_hidden('#skF_9',k8_relset_1('#skF_5','#skF_7','#skF_8','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3640,plain,(
    r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_3602])).

tff(c_3712,plain,(
    ! [D_746,A_747,B_748] :
      ( r2_hidden(k4_tarski(D_746,'#skF_4'(A_747,B_748,k10_relat_1(A_747,B_748),D_746)),A_747)
      | ~ r2_hidden(D_746,k10_relat_1(A_747,B_748))
      | ~ v1_relat_1(A_747) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4389,plain,(
    ! [D_858,A_859,B_860,A_861] :
      ( r2_hidden(k4_tarski(D_858,'#skF_4'(A_859,B_860,k10_relat_1(A_859,B_860),D_858)),A_861)
      | ~ m1_subset_1(A_859,k1_zfmisc_1(A_861))
      | ~ r2_hidden(D_858,k10_relat_1(A_859,B_860))
      | ~ v1_relat_1(A_859) ) ),
    inference(resolution,[status(thm)],[c_3712,c_8])).

tff(c_5555,plain,(
    ! [A_968,B_971,C_970,D_969,D_967] :
      ( r2_hidden('#skF_4'(A_968,B_971,k10_relat_1(A_968,B_971),D_967),D_969)
      | ~ m1_subset_1(A_968,k1_zfmisc_1(k2_zfmisc_1(C_970,D_969)))
      | ~ r2_hidden(D_967,k10_relat_1(A_968,B_971))
      | ~ v1_relat_1(A_968) ) ),
    inference(resolution,[status(thm)],[c_4389,c_4])).

tff(c_5617,plain,(
    ! [B_971,D_967] :
      ( r2_hidden('#skF_4'('#skF_8',B_971,k10_relat_1('#skF_8',B_971),D_967),'#skF_7')
      | ~ r2_hidden(D_967,k10_relat_1('#skF_8',B_971))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_5555])).

tff(c_5641,plain,(
    ! [B_972,D_973] :
      ( r2_hidden('#skF_4'('#skF_8',B_972,k10_relat_1('#skF_8',B_972),D_973),'#skF_7')
      | ~ r2_hidden(D_973,k10_relat_1('#skF_8',B_972)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_5617])).

tff(c_5658,plain,(
    ! [B_974,D_975] :
      ( m1_subset_1('#skF_4'('#skF_8',B_974,k10_relat_1('#skF_8',B_974),D_975),'#skF_7')
      | ~ r2_hidden(D_975,k10_relat_1('#skF_8',B_974)) ) ),
    inference(resolution,[status(thm)],[c_5641,c_10])).

tff(c_3603,plain,(
    ~ r2_hidden('#skF_10','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [F_150] :
      ( ~ r2_hidden(F_150,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_150),'#skF_8')
      | ~ m1_subset_1(F_150,'#skF_7')
      | r2_hidden('#skF_10','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3660,plain,(
    ! [F_150] :
      ( ~ r2_hidden(F_150,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',F_150),'#skF_8')
      | ~ m1_subset_1(F_150,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3603,c_50])).

tff(c_3718,plain,(
    ! [B_748] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_748,k10_relat_1('#skF_8',B_748),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_748,k10_relat_1('#skF_8',B_748),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_748))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3712,c_3660])).

tff(c_3877,plain,(
    ! [B_772] :
      ( ~ r2_hidden('#skF_4'('#skF_8',B_772,k10_relat_1('#skF_8',B_772),'#skF_9'),'#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_772,k10_relat_1('#skF_8',B_772),'#skF_9'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_772)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_3718])).

tff(c_3881,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7')
    | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_3877])).

tff(c_3884,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_6',k10_relat_1('#skF_8','#skF_6'),'#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_3640,c_3881])).

tff(c_5669,plain,(
    ~ r2_hidden('#skF_9',k10_relat_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_5658,c_3884])).

tff(c_5677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3640,c_5669])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.47/2.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.55  
% 7.47/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.56  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 7.47/2.56  
% 7.47/2.56  %Foreground sorts:
% 7.47/2.56  
% 7.47/2.56  
% 7.47/2.56  %Background operators:
% 7.47/2.56  
% 7.47/2.56  
% 7.47/2.56  %Foreground operators:
% 7.47/2.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.47/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.47/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.47/2.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.47/2.56  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 7.47/2.56  tff('#skF_7', type, '#skF_7': $i).
% 7.47/2.56  tff('#skF_10', type, '#skF_10': $i).
% 7.47/2.56  tff('#skF_5', type, '#skF_5': $i).
% 7.47/2.56  tff('#skF_6', type, '#skF_6': $i).
% 7.47/2.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.47/2.56  tff('#skF_9', type, '#skF_9': $i).
% 7.47/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.47/2.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.47/2.56  tff('#skF_8', type, '#skF_8': $i).
% 7.47/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.47/2.56  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.47/2.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.47/2.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.47/2.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.47/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.47/2.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.47/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.47/2.56  
% 7.47/2.58  tff(f_95, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 7.47/2.58  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 7.47/2.58  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.47/2.58  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.47/2.58  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 7.47/2.58  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 7.47/2.58  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 7.47/2.58  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.47/2.58  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.58  tff(c_3634, plain, (![A_714, B_715, C_716, D_717]: (k8_relset_1(A_714, B_715, C_716, D_717)=k10_relat_1(C_716, D_717) | ~m1_subset_1(C_716, k1_zfmisc_1(k2_zfmisc_1(A_714, B_715))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.47/2.58  tff(c_3637, plain, (![D_717]: (k8_relset_1('#skF_5', '#skF_7', '#skF_8', D_717)=k10_relat_1('#skF_8', D_717))), inference(resolution, [status(thm)], [c_38, c_3634])).
% 7.47/2.58  tff(c_2368, plain, (![A_498, B_499, C_500, D_501]: (k8_relset_1(A_498, B_499, C_500, D_501)=k10_relat_1(C_500, D_501) | ~m1_subset_1(C_500, k1_zfmisc_1(k2_zfmisc_1(A_498, B_499))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.47/2.58  tff(c_2371, plain, (![D_501]: (k8_relset_1('#skF_5', '#skF_7', '#skF_8', D_501)=k10_relat_1('#skF_8', D_501))), inference(resolution, [status(thm)], [c_38, c_2368])).
% 7.47/2.58  tff(c_305, plain, (![A_211, B_212, C_213, D_214]: (k8_relset_1(A_211, B_212, C_213, D_214)=k10_relat_1(C_213, D_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.47/2.58  tff(c_308, plain, (![D_214]: (k8_relset_1('#skF_5', '#skF_7', '#skF_8', D_214)=k10_relat_1('#skF_8', D_214))), inference(resolution, [status(thm)], [c_38, c_305])).
% 7.47/2.58  tff(c_60, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6')) | m1_subset_1('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.58  tff(c_81, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_60])).
% 7.47/2.58  tff(c_52, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6')) | r2_hidden('#skF_10', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.58  tff(c_70, plain, (r2_hidden('#skF_10', '#skF_6')), inference(splitLeft, [status(thm)], [c_52])).
% 7.47/2.58  tff(c_56, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.58  tff(c_83, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_56])).
% 7.47/2.58  tff(c_32, plain, (![A_56, B_57]: (v1_relat_1(k2_zfmisc_1(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.47/2.58  tff(c_63, plain, (![B_155, A_156]: (v1_relat_1(B_155) | ~m1_subset_1(B_155, k1_zfmisc_1(A_156)) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.47/2.58  tff(c_66, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_63])).
% 7.47/2.58  tff(c_69, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_66])).
% 7.47/2.58  tff(c_191, plain, (![D_193, A_194, B_195, E_196]: (r2_hidden(D_193, k10_relat_1(A_194, B_195)) | ~r2_hidden(E_196, B_195) | ~r2_hidden(k4_tarski(D_193, E_196), A_194) | ~v1_relat_1(A_194))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.47/2.58  tff(c_210, plain, (![D_197, A_198]: (r2_hidden(D_197, k10_relat_1(A_198, '#skF_6')) | ~r2_hidden(k4_tarski(D_197, '#skF_10'), A_198) | ~v1_relat_1(A_198))), inference(resolution, [status(thm)], [c_70, c_191])).
% 7.47/2.58  tff(c_220, plain, (r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_83, c_210])).
% 7.47/2.58  tff(c_227, plain, (r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_220])).
% 7.47/2.58  tff(c_164, plain, (![A_186, B_187, C_188, D_189]: (k8_relset_1(A_186, B_187, C_188, D_189)=k10_relat_1(C_188, D_189) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.47/2.58  tff(c_171, plain, (![D_189]: (k8_relset_1('#skF_5', '#skF_7', '#skF_8', D_189)=k10_relat_1('#skF_8', D_189))), inference(resolution, [status(thm)], [c_38, c_164])).
% 7.47/2.58  tff(c_46, plain, (![F_150]: (~r2_hidden(F_150, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_150), '#skF_8') | ~m1_subset_1(F_150, '#skF_7') | ~r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.58  tff(c_264, plain, (![F_205]: (~r2_hidden(F_205, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_205), '#skF_8') | ~m1_subset_1(F_205, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_171, c_46])).
% 7.47/2.58  tff(c_271, plain, (~r2_hidden('#skF_10', '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_83, c_264])).
% 7.47/2.58  tff(c_278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_70, c_271])).
% 7.47/2.58  tff(c_279, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6'))), inference(splitRight, [status(thm)], [c_56])).
% 7.47/2.58  tff(c_311, plain, (r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_279])).
% 7.47/2.58  tff(c_411, plain, (![D_249, A_250, B_251]: (r2_hidden(k4_tarski(D_249, '#skF_4'(A_250, B_251, k10_relat_1(A_250, B_251), D_249)), A_250) | ~r2_hidden(D_249, k10_relat_1(A_250, B_251)) | ~v1_relat_1(A_250))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.47/2.58  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.47/2.58  tff(c_1125, plain, (![D_369, A_370, B_371, A_372]: (r2_hidden(k4_tarski(D_369, '#skF_4'(A_370, B_371, k10_relat_1(A_370, B_371), D_369)), A_372) | ~m1_subset_1(A_370, k1_zfmisc_1(A_372)) | ~r2_hidden(D_369, k10_relat_1(A_370, B_371)) | ~v1_relat_1(A_370))), inference(resolution, [status(thm)], [c_411, c_8])).
% 7.47/2.58  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.47/2.58  tff(c_2161, plain, (![B_473, D_471, A_475, C_474, D_472]: (r2_hidden('#skF_4'(A_475, B_473, k10_relat_1(A_475, B_473), D_472), D_471) | ~m1_subset_1(A_475, k1_zfmisc_1(k2_zfmisc_1(C_474, D_471))) | ~r2_hidden(D_472, k10_relat_1(A_475, B_473)) | ~v1_relat_1(A_475))), inference(resolution, [status(thm)], [c_1125, c_4])).
% 7.47/2.58  tff(c_2217, plain, (![B_473, D_472]: (r2_hidden('#skF_4'('#skF_8', B_473, k10_relat_1('#skF_8', B_473), D_472), '#skF_7') | ~r2_hidden(D_472, k10_relat_1('#skF_8', B_473)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_2161])).
% 7.47/2.58  tff(c_2239, plain, (![B_476, D_477]: (r2_hidden('#skF_4'('#skF_8', B_476, k10_relat_1('#skF_8', B_476), D_477), '#skF_7') | ~r2_hidden(D_477, k10_relat_1('#skF_8', B_476)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2217])).
% 7.47/2.58  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.47/2.58  tff(c_2250, plain, (![B_478, D_479]: (m1_subset_1('#skF_4'('#skF_8', B_478, k10_relat_1('#skF_8', B_478), D_479), '#skF_7') | ~r2_hidden(D_479, k10_relat_1('#skF_8', B_478)))), inference(resolution, [status(thm)], [c_2239, c_10])).
% 7.47/2.58  tff(c_16, plain, (![A_14, B_37, D_52]: (r2_hidden('#skF_4'(A_14, B_37, k10_relat_1(A_14, B_37), D_52), B_37) | ~r2_hidden(D_52, k10_relat_1(A_14, B_37)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.47/2.58  tff(c_280, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_56])).
% 7.47/2.58  tff(c_54, plain, (![F_150]: (~r2_hidden(F_150, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_150), '#skF_8') | ~m1_subset_1(F_150, '#skF_7') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.58  tff(c_343, plain, (![F_150]: (~r2_hidden(F_150, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_150), '#skF_8') | ~m1_subset_1(F_150, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_280, c_54])).
% 7.47/2.58  tff(c_415, plain, (![B_251]: (~r2_hidden('#skF_4'('#skF_8', B_251, k10_relat_1('#skF_8', B_251), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_251, k10_relat_1('#skF_8', B_251), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_251)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_411, c_343])).
% 7.47/2.58  tff(c_477, plain, (![B_263]: (~r2_hidden('#skF_4'('#skF_8', B_263, k10_relat_1('#skF_8', B_263), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_263, k10_relat_1('#skF_8', B_263), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_263)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_415])).
% 7.47/2.58  tff(c_481, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_16, c_477])).
% 7.47/2.58  tff(c_484, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_311, c_481])).
% 7.47/2.58  tff(c_2261, plain, (~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_2250, c_484])).
% 7.47/2.58  tff(c_2269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_311, c_2261])).
% 7.47/2.58  tff(c_2271, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_60])).
% 7.47/2.58  tff(c_2272, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_56])).
% 7.47/2.58  tff(c_2304, plain, (![A_485]: (r2_hidden(k4_tarski('#skF_9', '#skF_10'), A_485) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_485)))), inference(resolution, [status(thm)], [c_2272, c_8])).
% 7.47/2.58  tff(c_2322, plain, (![D_486, C_487]: (r2_hidden('#skF_10', D_486) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(C_487, D_486))))), inference(resolution, [status(thm)], [c_2304, c_4])).
% 7.47/2.58  tff(c_2326, plain, (r2_hidden('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_2322])).
% 7.47/2.58  tff(c_2332, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_2326, c_10])).
% 7.47/2.58  tff(c_2337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2271, c_2332])).
% 7.47/2.58  tff(c_2338, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6'))), inference(splitRight, [status(thm)], [c_56])).
% 7.47/2.58  tff(c_2374, plain, (r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2371, c_2338])).
% 7.47/2.58  tff(c_2505, plain, (![D_542, A_543, B_544]: (r2_hidden(k4_tarski(D_542, '#skF_4'(A_543, B_544, k10_relat_1(A_543, B_544), D_542)), A_543) | ~r2_hidden(D_542, k10_relat_1(A_543, B_544)) | ~v1_relat_1(A_543))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.47/2.58  tff(c_2899, plain, (![D_606, A_607, B_608, A_609]: (r2_hidden(k4_tarski(D_606, '#skF_4'(A_607, B_608, k10_relat_1(A_607, B_608), D_606)), A_609) | ~m1_subset_1(A_607, k1_zfmisc_1(A_609)) | ~r2_hidden(D_606, k10_relat_1(A_607, B_608)) | ~v1_relat_1(A_607))), inference(resolution, [status(thm)], [c_2505, c_8])).
% 7.47/2.58  tff(c_3525, plain, (![D_687, A_685, B_688, C_689, D_686]: (r2_hidden('#skF_4'(A_685, B_688, k10_relat_1(A_685, B_688), D_687), D_686) | ~m1_subset_1(A_685, k1_zfmisc_1(k2_zfmisc_1(C_689, D_686))) | ~r2_hidden(D_687, k10_relat_1(A_685, B_688)) | ~v1_relat_1(A_685))), inference(resolution, [status(thm)], [c_2899, c_4])).
% 7.47/2.58  tff(c_3557, plain, (![B_688, D_687]: (r2_hidden('#skF_4'('#skF_8', B_688, k10_relat_1('#skF_8', B_688), D_687), '#skF_7') | ~r2_hidden(D_687, k10_relat_1('#skF_8', B_688)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_3525])).
% 7.47/2.58  tff(c_3571, plain, (![B_690, D_691]: (r2_hidden('#skF_4'('#skF_8', B_690, k10_relat_1('#skF_8', B_690), D_691), '#skF_7') | ~r2_hidden(D_691, k10_relat_1('#skF_8', B_690)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_3557])).
% 7.47/2.58  tff(c_3582, plain, (![B_692, D_693]: (m1_subset_1('#skF_4'('#skF_8', B_692, k10_relat_1('#skF_8', B_692), D_693), '#skF_7') | ~r2_hidden(D_693, k10_relat_1('#skF_8', B_692)))), inference(resolution, [status(thm)], [c_3571, c_10])).
% 7.47/2.58  tff(c_58, plain, (![F_150]: (~r2_hidden(F_150, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_150), '#skF_8') | ~m1_subset_1(F_150, '#skF_7') | m1_subset_1('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.58  tff(c_2392, plain, (![F_150]: (~r2_hidden(F_150, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_150), '#skF_8') | ~m1_subset_1(F_150, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_2271, c_58])).
% 7.47/2.58  tff(c_2511, plain, (![B_544]: (~r2_hidden('#skF_4'('#skF_8', B_544, k10_relat_1('#skF_8', B_544), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_544, k10_relat_1('#skF_8', B_544), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_544)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_2505, c_2392])).
% 7.47/2.58  tff(c_2657, plain, (![B_565]: (~r2_hidden('#skF_4'('#skF_8', B_565, k10_relat_1('#skF_8', B_565), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_565, k10_relat_1('#skF_8', B_565), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_565)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2511])).
% 7.47/2.58  tff(c_2661, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_16, c_2657])).
% 7.47/2.58  tff(c_2664, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_2374, c_2661])).
% 7.47/2.58  tff(c_3593, plain, (~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_3582, c_2664])).
% 7.47/2.58  tff(c_3601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2374, c_3593])).
% 7.47/2.58  tff(c_3602, plain, (r2_hidden('#skF_9', k8_relset_1('#skF_5', '#skF_7', '#skF_8', '#skF_6'))), inference(splitRight, [status(thm)], [c_52])).
% 7.47/2.58  tff(c_3640, plain, (r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3637, c_3602])).
% 7.47/2.58  tff(c_3712, plain, (![D_746, A_747, B_748]: (r2_hidden(k4_tarski(D_746, '#skF_4'(A_747, B_748, k10_relat_1(A_747, B_748), D_746)), A_747) | ~r2_hidden(D_746, k10_relat_1(A_747, B_748)) | ~v1_relat_1(A_747))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.47/2.58  tff(c_4389, plain, (![D_858, A_859, B_860, A_861]: (r2_hidden(k4_tarski(D_858, '#skF_4'(A_859, B_860, k10_relat_1(A_859, B_860), D_858)), A_861) | ~m1_subset_1(A_859, k1_zfmisc_1(A_861)) | ~r2_hidden(D_858, k10_relat_1(A_859, B_860)) | ~v1_relat_1(A_859))), inference(resolution, [status(thm)], [c_3712, c_8])).
% 7.47/2.58  tff(c_5555, plain, (![A_968, B_971, C_970, D_969, D_967]: (r2_hidden('#skF_4'(A_968, B_971, k10_relat_1(A_968, B_971), D_967), D_969) | ~m1_subset_1(A_968, k1_zfmisc_1(k2_zfmisc_1(C_970, D_969))) | ~r2_hidden(D_967, k10_relat_1(A_968, B_971)) | ~v1_relat_1(A_968))), inference(resolution, [status(thm)], [c_4389, c_4])).
% 7.47/2.58  tff(c_5617, plain, (![B_971, D_967]: (r2_hidden('#skF_4'('#skF_8', B_971, k10_relat_1('#skF_8', B_971), D_967), '#skF_7') | ~r2_hidden(D_967, k10_relat_1('#skF_8', B_971)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_5555])).
% 7.47/2.58  tff(c_5641, plain, (![B_972, D_973]: (r2_hidden('#skF_4'('#skF_8', B_972, k10_relat_1('#skF_8', B_972), D_973), '#skF_7') | ~r2_hidden(D_973, k10_relat_1('#skF_8', B_972)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_5617])).
% 7.47/2.58  tff(c_5658, plain, (![B_974, D_975]: (m1_subset_1('#skF_4'('#skF_8', B_974, k10_relat_1('#skF_8', B_974), D_975), '#skF_7') | ~r2_hidden(D_975, k10_relat_1('#skF_8', B_974)))), inference(resolution, [status(thm)], [c_5641, c_10])).
% 7.47/2.58  tff(c_3603, plain, (~r2_hidden('#skF_10', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 7.47/2.58  tff(c_50, plain, (![F_150]: (~r2_hidden(F_150, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_150), '#skF_8') | ~m1_subset_1(F_150, '#skF_7') | r2_hidden('#skF_10', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.47/2.58  tff(c_3660, plain, (![F_150]: (~r2_hidden(F_150, '#skF_6') | ~r2_hidden(k4_tarski('#skF_9', F_150), '#skF_8') | ~m1_subset_1(F_150, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_3603, c_50])).
% 7.47/2.58  tff(c_3718, plain, (![B_748]: (~r2_hidden('#skF_4'('#skF_8', B_748, k10_relat_1('#skF_8', B_748), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_748, k10_relat_1('#skF_8', B_748), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_748)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_3712, c_3660])).
% 7.47/2.58  tff(c_3877, plain, (![B_772]: (~r2_hidden('#skF_4'('#skF_8', B_772, k10_relat_1('#skF_8', B_772), '#skF_9'), '#skF_6') | ~m1_subset_1('#skF_4'('#skF_8', B_772, k10_relat_1('#skF_8', B_772), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_772)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_3718])).
% 7.47/2.58  tff(c_3881, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_16, c_3877])).
% 7.47/2.58  tff(c_3884, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_6', k10_relat_1('#skF_8', '#skF_6'), '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_3640, c_3881])).
% 7.47/2.58  tff(c_5669, plain, (~r2_hidden('#skF_9', k10_relat_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_5658, c_3884])).
% 7.47/2.58  tff(c_5677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3640, c_5669])).
% 7.47/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.58  
% 7.47/2.58  Inference rules
% 7.47/2.58  ----------------------
% 7.47/2.58  #Ref     : 0
% 7.47/2.58  #Sup     : 1269
% 7.47/2.58  #Fact    : 0
% 7.47/2.58  #Define  : 0
% 7.47/2.58  #Split   : 15
% 7.47/2.58  #Chain   : 0
% 7.47/2.58  #Close   : 0
% 7.47/2.58  
% 7.47/2.58  Ordering : KBO
% 7.47/2.58  
% 7.47/2.58  Simplification rules
% 7.47/2.58  ----------------------
% 7.47/2.58  #Subsume      : 35
% 7.47/2.58  #Demod        : 144
% 7.47/2.58  #Tautology    : 44
% 7.47/2.58  #SimpNegUnit  : 5
% 7.47/2.58  #BackRed      : 9
% 7.47/2.58  
% 7.47/2.58  #Partial instantiations: 0
% 7.47/2.58  #Strategies tried      : 1
% 7.47/2.58  
% 7.47/2.58  Timing (in seconds)
% 7.47/2.58  ----------------------
% 7.73/2.58  Preprocessing        : 0.33
% 7.73/2.58  Parsing              : 0.17
% 7.73/2.58  CNF conversion       : 0.04
% 7.73/2.58  Main loop            : 1.43
% 7.73/2.59  Inferencing          : 0.53
% 7.73/2.59  Reduction            : 0.36
% 7.73/2.59  Demodulation         : 0.24
% 7.73/2.59  BG Simplification    : 0.07
% 7.73/2.59  Subsumption          : 0.33
% 7.73/2.59  Abstraction          : 0.10
% 7.73/2.59  MUC search           : 0.00
% 7.73/2.59  Cooper               : 0.00
% 7.73/2.59  Total                : 1.81
% 7.73/2.59  Index Insertion      : 0.00
% 7.73/2.59  Index Deletion       : 0.00
% 7.73/2.59  Index Matching       : 0.00
% 7.73/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
