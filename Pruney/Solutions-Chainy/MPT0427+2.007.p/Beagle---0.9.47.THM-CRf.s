%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:57 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 382 expanded)
%              Number of leaves         :   29 ( 135 expanded)
%              Depth                    :   11
%              Number of atoms          :  138 ( 809 expanded)
%              Number of equality atoms :   45 ( 250 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_165,plain,(
    ! [A_53,B_54] :
      ( k6_setfam_1(A_53,B_54) = k1_setfam_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_177,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_165])).

tff(c_276,plain,(
    ! [A_69,B_70] :
      ( k8_setfam_1(A_69,B_70) = k6_setfam_1(A_69,B_70)
      | k1_xboole_0 = B_70
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_287,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_276])).

tff(c_294,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_287])).

tff(c_297,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_123,plain,(
    ! [A_48,B_49,C_50] :
      ( ~ r1_xboole_0(A_48,B_49)
      | ~ r2_hidden(C_50,B_49)
      | ~ r2_hidden(C_50,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_133,plain,(
    ! [C_51] : ~ r2_hidden(C_51,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_123])).

tff(c_148,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_303,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_148])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_178,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_165])).

tff(c_290,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_276])).

tff(c_296,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_290])).

tff(c_312,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_296])).

tff(c_313,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_36,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_68,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_104,plain,(
    ! [A_45,B_46] :
      ( v1_xboole_0(A_45)
      | ~ v1_xboole_0(B_46)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_30,c_68])).

tff(c_116,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_104])).

tff(c_117,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_316,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_117])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_316])).

tff(c_326,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_214,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k8_setfam_1(A_61,B_62),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_228,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k8_setfam_1(A_63,B_64),A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(resolution,[status(thm)],[c_214,c_28])).

tff(c_242,plain,(
    r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_228])).

tff(c_384,plain,(
    r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_242])).

tff(c_55,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_66,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_118,plain,(
    ! [A_47] :
      ( k8_setfam_1(A_47,k1_xboole_0) = A_47
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_122,plain,(
    ! [A_47] :
      ( k8_setfam_1(A_47,k1_xboole_0) = A_47
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_30,c_118])).

tff(c_414,plain,(
    ! [A_76] :
      ( k8_setfam_1(A_76,'#skF_4') = A_76
      | ~ r1_tarski('#skF_4',k1_zfmisc_1(A_76)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_297,c_122])).

tff(c_418,plain,(
    k8_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_414])).

tff(c_34,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_385,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_34])).

tff(c_428,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_385])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_428])).

tff(c_434,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_setfam_1(B_24),k1_setfam_1(A_23))
      | k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_465,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_472,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_148])).

tff(c_478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_472])).

tff(c_479,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_433,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_436,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_34])).

tff(c_481,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_436])).

tff(c_504,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_481])).

tff(c_507,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_504])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_507])).

tff(c_510,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_515,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_510,c_6])).

tff(c_20,plain,(
    ! [A_15] :
      ( k8_setfam_1(A_15,k1_xboole_0) = A_15
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_541,plain,(
    ! [A_78] :
      ( k8_setfam_1(A_78,'#skF_4') = A_78
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_78))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_515,c_20])).

tff(c_549,plain,(
    k8_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_40,c_541])).

tff(c_511,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_519,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_511,c_6])).

tff(c_527,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_519])).

tff(c_530,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_34])).

tff(c_566,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_549,c_530])).

tff(c_663,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(k8_setfam_1(A_94,B_95),k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(A_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_676,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_663])).

tff(c_681,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_676])).

tff(c_687,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_681,c_28])).

tff(c_692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:57:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  
% 2.77/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.77/1.38  
% 2.77/1.38  %Foreground sorts:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Background operators:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Foreground operators:
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.77/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.38  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.77/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.38  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.77/1.38  
% 2.77/1.40  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.77/1.40  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.77/1.40  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.77/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.77/1.40  tff(f_65, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.77/1.40  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.77/1.40  tff(f_95, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.77/1.40  tff(f_72, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.77/1.40  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.77/1.40  tff(f_101, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.77/1.40  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.77/1.40  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.77/1.40  tff(c_165, plain, (![A_53, B_54]: (k6_setfam_1(A_53, B_54)=k1_setfam_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.77/1.40  tff(c_177, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_165])).
% 2.77/1.40  tff(c_276, plain, (![A_69, B_70]: (k8_setfam_1(A_69, B_70)=k6_setfam_1(A_69, B_70) | k1_xboole_0=B_70 | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.40  tff(c_287, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_276])).
% 2.77/1.40  tff(c_294, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_287])).
% 2.77/1.40  tff(c_297, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_294])).
% 2.77/1.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.40  tff(c_14, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.77/1.40  tff(c_123, plain, (![A_48, B_49, C_50]: (~r1_xboole_0(A_48, B_49) | ~r2_hidden(C_50, B_49) | ~r2_hidden(C_50, A_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.77/1.40  tff(c_133, plain, (![C_51]: (~r2_hidden(C_51, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_123])).
% 2.77/1.40  tff(c_148, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_133])).
% 2.77/1.40  tff(c_303, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_297, c_148])).
% 2.77/1.40  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.77/1.40  tff(c_178, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_165])).
% 2.77/1.40  tff(c_290, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_38, c_276])).
% 2.77/1.40  tff(c_296, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_290])).
% 2.77/1.40  tff(c_312, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_297, c_296])).
% 2.77/1.40  tff(c_313, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_312])).
% 2.77/1.40  tff(c_36, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.77/1.40  tff(c_30, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.77/1.40  tff(c_68, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.77/1.40  tff(c_104, plain, (![A_45, B_46]: (v1_xboole_0(A_45) | ~v1_xboole_0(B_46) | ~r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_30, c_68])).
% 2.77/1.40  tff(c_116, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_104])).
% 2.77/1.40  tff(c_117, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_116])).
% 2.77/1.40  tff(c_316, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_117])).
% 2.77/1.40  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_303, c_316])).
% 2.77/1.40  tff(c_326, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_312])).
% 2.77/1.40  tff(c_214, plain, (![A_61, B_62]: (m1_subset_1(k8_setfam_1(A_61, B_62), k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.77/1.40  tff(c_28, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.77/1.40  tff(c_228, plain, (![A_63, B_64]: (r1_tarski(k8_setfam_1(A_63, B_64), A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(resolution, [status(thm)], [c_214, c_28])).
% 2.77/1.40  tff(c_242, plain, (r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_38, c_228])).
% 2.77/1.40  tff(c_384, plain, (r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_242])).
% 2.77/1.40  tff(c_55, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.77/1.40  tff(c_66, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_55])).
% 2.77/1.40  tff(c_118, plain, (![A_47]: (k8_setfam_1(A_47, k1_xboole_0)=A_47 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.40  tff(c_122, plain, (![A_47]: (k8_setfam_1(A_47, k1_xboole_0)=A_47 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_30, c_118])).
% 2.77/1.40  tff(c_414, plain, (![A_76]: (k8_setfam_1(A_76, '#skF_4')=A_76 | ~r1_tarski('#skF_4', k1_zfmisc_1(A_76)))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_297, c_122])).
% 2.77/1.40  tff(c_418, plain, (k8_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_66, c_414])).
% 2.77/1.40  tff(c_34, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.77/1.40  tff(c_385, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_326, c_34])).
% 2.77/1.40  tff(c_428, plain, (~r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_418, c_385])).
% 2.77/1.40  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_384, c_428])).
% 2.77/1.40  tff(c_434, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_294])).
% 2.77/1.40  tff(c_32, plain, (![B_24, A_23]: (r1_tarski(k1_setfam_1(B_24), k1_setfam_1(A_23)) | k1_xboole_0=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.77/1.40  tff(c_465, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_296])).
% 2.77/1.40  tff(c_472, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_148])).
% 2.77/1.40  tff(c_478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_472])).
% 2.77/1.40  tff(c_479, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_296])).
% 2.77/1.40  tff(c_433, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_294])).
% 2.77/1.40  tff(c_436, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_34])).
% 2.77/1.40  tff(c_481, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_436])).
% 2.77/1.40  tff(c_504, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_481])).
% 2.77/1.40  tff(c_507, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_504])).
% 2.77/1.40  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_507])).
% 2.77/1.40  tff(c_510, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_116])).
% 2.77/1.40  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.40  tff(c_515, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_510, c_6])).
% 2.77/1.40  tff(c_20, plain, (![A_15]: (k8_setfam_1(A_15, k1_xboole_0)=A_15 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.40  tff(c_541, plain, (![A_78]: (k8_setfam_1(A_78, '#skF_4')=A_78 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_78))))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_515, c_20])).
% 2.77/1.40  tff(c_549, plain, (k8_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_40, c_541])).
% 2.77/1.40  tff(c_511, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_116])).
% 2.77/1.40  tff(c_519, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_511, c_6])).
% 2.77/1.40  tff(c_527, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_515, c_519])).
% 2.77/1.40  tff(c_530, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_527, c_34])).
% 2.77/1.40  tff(c_566, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_549, c_549, c_530])).
% 2.77/1.40  tff(c_663, plain, (![A_94, B_95]: (m1_subset_1(k8_setfam_1(A_94, B_95), k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(A_94))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.77/1.40  tff(c_676, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_549, c_663])).
% 2.77/1.40  tff(c_681, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_676])).
% 2.77/1.40  tff(c_687, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_681, c_28])).
% 2.77/1.40  tff(c_692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_566, c_687])).
% 2.77/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.40  
% 2.77/1.40  Inference rules
% 2.77/1.40  ----------------------
% 2.77/1.40  #Ref     : 0
% 2.77/1.40  #Sup     : 128
% 2.77/1.40  #Fact    : 0
% 2.77/1.40  #Define  : 0
% 2.77/1.40  #Split   : 6
% 2.77/1.40  #Chain   : 0
% 2.77/1.40  #Close   : 0
% 2.77/1.40  
% 2.77/1.40  Ordering : KBO
% 2.77/1.40  
% 2.77/1.40  Simplification rules
% 2.77/1.40  ----------------------
% 2.77/1.40  #Subsume      : 28
% 2.77/1.40  #Demod        : 91
% 2.77/1.40  #Tautology    : 55
% 2.77/1.40  #SimpNegUnit  : 3
% 2.77/1.40  #BackRed      : 44
% 2.77/1.40  
% 2.77/1.40  #Partial instantiations: 0
% 2.77/1.40  #Strategies tried      : 1
% 2.77/1.40  
% 2.77/1.40  Timing (in seconds)
% 2.77/1.40  ----------------------
% 2.77/1.40  Preprocessing        : 0.32
% 2.77/1.40  Parsing              : 0.18
% 2.77/1.40  CNF conversion       : 0.02
% 2.77/1.40  Main loop            : 0.30
% 2.77/1.40  Inferencing          : 0.11
% 2.77/1.40  Reduction            : 0.09
% 2.77/1.40  Demodulation         : 0.06
% 2.77/1.40  BG Simplification    : 0.02
% 2.77/1.40  Subsumption          : 0.05
% 2.77/1.40  Abstraction          : 0.02
% 2.77/1.40  MUC search           : 0.00
% 2.77/1.40  Cooper               : 0.00
% 2.77/1.40  Total                : 0.67
% 2.77/1.40  Index Insertion      : 0.00
% 2.77/1.40  Index Deletion       : 0.00
% 2.77/1.40  Index Matching       : 0.00
% 2.77/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
