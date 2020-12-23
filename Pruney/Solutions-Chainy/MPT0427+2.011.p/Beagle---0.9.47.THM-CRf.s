%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:57 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 457 expanded)
%              Number of leaves         :   26 ( 155 expanded)
%              Depth                    :   12
%              Number of atoms          :  128 ( 932 expanded)
%              Number of equality atoms :   42 ( 260 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,(
    ! [B_30,A_31] :
      ( v1_xboole_0(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_97,plain,(
    ! [A_34,B_35] :
      ( v1_xboole_0(A_34)
      | ~ v1_xboole_0(B_35)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_22,c_66])).

tff(c_114,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_97])).

tff(c_115,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_116,plain,(
    ! [A_36,B_37] :
      ( k6_setfam_1(A_36,B_37) = k1_setfam_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_128,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_116])).

tff(c_231,plain,(
    ! [A_49,B_50] :
      ( k8_setfam_1(A_49,B_50) = k6_setfam_1(A_49,B_50)
      | k1_xboole_0 = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_246,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_231])).

tff(c_255,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_246])).

tff(c_258,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_129,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_116])).

tff(c_249,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_231])).

tff(c_257,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_249])).

tff(c_272,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_257])).

tff(c_273,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [B_27,A_28] :
      ( ~ r1_xboole_0(B_27,A_28)
      | ~ r1_tarski(B_27,A_28)
      | v1_xboole_0(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    ! [A_29] :
      ( ~ r1_tarski(A_29,k1_xboole_0)
      | v1_xboole_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_55])).

tff(c_263,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_60])).

tff(c_274,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_263])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_274])).

tff(c_283,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_79,plain,(
    ! [A_32] :
      ( k8_setfam_1(A_32,k1_xboole_0) = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,(
    ! [A_32] :
      ( k8_setfam_1(A_32,k1_xboole_0) = A_32
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_32)) ) ),
    inference(resolution,[status(thm)],[c_22,c_79])).

tff(c_85,plain,(
    ! [A_32] : k8_setfam_1(A_32,k1_xboole_0) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_82])).

tff(c_262,plain,(
    ! [A_32] : k8_setfam_1(A_32,'#skF_2') = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_85])).

tff(c_26,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_309,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_26])).

tff(c_336,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_309])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k8_setfam_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_340,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_16])).

tff(c_344,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_340])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_360,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_344,c_20])).

tff(c_365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_360])).

tff(c_367,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_24,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_setfam_1(B_18),k1_setfam_1(A_17))
      | k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_391,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_397,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_60])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_397])).

tff(c_404,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_366,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_368,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_26])).

tff(c_406,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_368])).

tff(c_418,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_406])).

tff(c_421,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_418])).

tff(c_423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_421])).

tff(c_425,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_433,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_425,c_2])).

tff(c_424,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_429,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_424,c_2])).

tff(c_445,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_429])).

tff(c_438,plain,(
    ! [A_2] : r1_tarski('#skF_2',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_4])).

tff(c_462,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_438])).

tff(c_434,plain,(
    ! [A_32] : k8_setfam_1(A_32,'#skF_2') = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_85])).

tff(c_494,plain,(
    ! [A_32] : k8_setfam_1(A_32,'#skF_3') = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_434])).

tff(c_537,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k8_setfam_1(A_69,B_70),k1_zfmisc_1(A_69))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_554,plain,(
    ! [A_71] :
      ( m1_subset_1(A_71,k1_zfmisc_1(A_71))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_537])).

tff(c_557,plain,(
    ! [A_71] :
      ( m1_subset_1(A_71,k1_zfmisc_1(A_71))
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_71)) ) ),
    inference(resolution,[status(thm)],[c_22,c_554])).

tff(c_565,plain,(
    ! [A_72] : m1_subset_1(A_72,k1_zfmisc_1(A_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_557])).

tff(c_578,plain,(
    ! [A_72] : r1_tarski(A_72,A_72) ),
    inference(resolution,[status(thm)],[c_565,c_20])).

tff(c_451,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_26])).

tff(c_508,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_494,c_451])).

tff(c_581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:10:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.36  
% 2.52/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.36  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.52/1.36  
% 2.52/1.36  %Foreground sorts:
% 2.52/1.36  
% 2.52/1.36  
% 2.52/1.36  %Background operators:
% 2.52/1.36  
% 2.52/1.36  
% 2.52/1.36  %Foreground operators:
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.36  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.52/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.52/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.36  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.52/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.52/1.36  
% 2.72/1.38  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.72/1.38  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.72/1.38  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.72/1.38  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.72/1.38  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.72/1.38  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.72/1.38  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.72/1.38  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.72/1.38  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.72/1.38  tff(f_77, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.72/1.38  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.72/1.38  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.72/1.38  tff(c_22, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.72/1.38  tff(c_66, plain, (![B_30, A_31]: (v1_xboole_0(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.72/1.38  tff(c_97, plain, (![A_34, B_35]: (v1_xboole_0(A_34) | ~v1_xboole_0(B_35) | ~r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_22, c_66])).
% 2.72/1.38  tff(c_114, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_97])).
% 2.72/1.38  tff(c_115, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_114])).
% 2.72/1.38  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.72/1.38  tff(c_116, plain, (![A_36, B_37]: (k6_setfam_1(A_36, B_37)=k1_setfam_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.38  tff(c_128, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_116])).
% 2.72/1.38  tff(c_231, plain, (![A_49, B_50]: (k8_setfam_1(A_49, B_50)=k6_setfam_1(A_49, B_50) | k1_xboole_0=B_50 | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.72/1.38  tff(c_246, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_231])).
% 2.72/1.38  tff(c_255, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_246])).
% 2.72/1.38  tff(c_258, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_255])).
% 2.72/1.38  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.72/1.38  tff(c_129, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_116])).
% 2.72/1.38  tff(c_249, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_231])).
% 2.72/1.38  tff(c_257, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_249])).
% 2.72/1.38  tff(c_272, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_258, c_257])).
% 2.72/1.38  tff(c_273, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_272])).
% 2.72/1.38  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.38  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.38  tff(c_50, plain, (![B_27, A_28]: (~r1_xboole_0(B_27, A_28) | ~r1_tarski(B_27, A_28) | v1_xboole_0(B_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.72/1.38  tff(c_55, plain, (![A_29]: (~r1_tarski(A_29, k1_xboole_0) | v1_xboole_0(A_29))), inference(resolution, [status(thm)], [c_6, c_50])).
% 2.72/1.38  tff(c_60, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_55])).
% 2.72/1.38  tff(c_263, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_60])).
% 2.72/1.38  tff(c_274, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_263])).
% 2.72/1.38  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_274])).
% 2.72/1.38  tff(c_283, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_272])).
% 2.72/1.38  tff(c_79, plain, (![A_32]: (k8_setfam_1(A_32, k1_xboole_0)=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_32))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.72/1.38  tff(c_82, plain, (![A_32]: (k8_setfam_1(A_32, k1_xboole_0)=A_32 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_32)))), inference(resolution, [status(thm)], [c_22, c_79])).
% 2.72/1.38  tff(c_85, plain, (![A_32]: (k8_setfam_1(A_32, k1_xboole_0)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_82])).
% 2.72/1.38  tff(c_262, plain, (![A_32]: (k8_setfam_1(A_32, '#skF_2')=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_258, c_85])).
% 2.72/1.38  tff(c_26, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.72/1.38  tff(c_309, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_26])).
% 2.72/1.38  tff(c_336, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_309])).
% 2.72/1.38  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(k8_setfam_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.72/1.38  tff(c_340, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_283, c_16])).
% 2.72/1.38  tff(c_344, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_340])).
% 2.72/1.38  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.72/1.38  tff(c_360, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_344, c_20])).
% 2.72/1.38  tff(c_365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_336, c_360])).
% 2.72/1.38  tff(c_367, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_255])).
% 2.72/1.38  tff(c_24, plain, (![B_18, A_17]: (r1_tarski(k1_setfam_1(B_18), k1_setfam_1(A_17)) | k1_xboole_0=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.38  tff(c_391, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_257])).
% 2.72/1.38  tff(c_397, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_391, c_60])).
% 2.72/1.38  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_397])).
% 2.72/1.38  tff(c_404, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_257])).
% 2.72/1.38  tff(c_366, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_255])).
% 2.72/1.38  tff(c_368, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_26])).
% 2.72/1.38  tff(c_406, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_368])).
% 2.72/1.38  tff(c_418, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_406])).
% 2.72/1.38  tff(c_421, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_418])).
% 2.72/1.38  tff(c_423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_367, c_421])).
% 2.72/1.38  tff(c_425, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_114])).
% 2.72/1.38  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.38  tff(c_433, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_425, c_2])).
% 2.72/1.38  tff(c_424, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_114])).
% 2.72/1.38  tff(c_429, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_424, c_2])).
% 2.72/1.38  tff(c_445, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_433, c_429])).
% 2.72/1.38  tff(c_438, plain, (![A_2]: (r1_tarski('#skF_2', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_4])).
% 2.72/1.38  tff(c_462, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_438])).
% 2.72/1.38  tff(c_434, plain, (![A_32]: (k8_setfam_1(A_32, '#skF_2')=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_429, c_85])).
% 2.72/1.38  tff(c_494, plain, (![A_32]: (k8_setfam_1(A_32, '#skF_3')=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_445, c_434])).
% 2.72/1.38  tff(c_537, plain, (![A_69, B_70]: (m1_subset_1(k8_setfam_1(A_69, B_70), k1_zfmisc_1(A_69)) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.72/1.38  tff(c_554, plain, (![A_71]: (m1_subset_1(A_71, k1_zfmisc_1(A_71)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_71))))), inference(superposition, [status(thm), theory('equality')], [c_494, c_537])).
% 2.72/1.38  tff(c_557, plain, (![A_71]: (m1_subset_1(A_71, k1_zfmisc_1(A_71)) | ~r1_tarski('#skF_3', k1_zfmisc_1(A_71)))), inference(resolution, [status(thm)], [c_22, c_554])).
% 2.72/1.38  tff(c_565, plain, (![A_72]: (m1_subset_1(A_72, k1_zfmisc_1(A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_557])).
% 2.72/1.38  tff(c_578, plain, (![A_72]: (r1_tarski(A_72, A_72))), inference(resolution, [status(thm)], [c_565, c_20])).
% 2.72/1.38  tff(c_451, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_26])).
% 2.72/1.38  tff(c_508, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_494, c_494, c_451])).
% 2.72/1.38  tff(c_581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_578, c_508])).
% 2.72/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.38  
% 2.72/1.38  Inference rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Ref     : 0
% 2.72/1.38  #Sup     : 106
% 2.72/1.38  #Fact    : 0
% 2.72/1.38  #Define  : 0
% 2.72/1.38  #Split   : 6
% 2.72/1.38  #Chain   : 0
% 2.72/1.38  #Close   : 0
% 2.72/1.38  
% 2.72/1.38  Ordering : KBO
% 2.72/1.38  
% 2.72/1.38  Simplification rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Subsume      : 6
% 2.72/1.38  #Demod        : 90
% 2.72/1.38  #Tautology    : 66
% 2.72/1.38  #SimpNegUnit  : 4
% 2.72/1.38  #BackRed      : 43
% 2.72/1.38  
% 2.72/1.38  #Partial instantiations: 0
% 2.72/1.38  #Strategies tried      : 1
% 2.72/1.38  
% 2.72/1.38  Timing (in seconds)
% 2.72/1.38  ----------------------
% 2.72/1.38  Preprocessing        : 0.31
% 2.72/1.38  Parsing              : 0.16
% 2.72/1.38  CNF conversion       : 0.02
% 2.72/1.38  Main loop            : 0.29
% 2.72/1.38  Inferencing          : 0.10
% 2.72/1.38  Reduction            : 0.10
% 2.72/1.38  Demodulation         : 0.07
% 2.72/1.38  BG Simplification    : 0.02
% 2.72/1.38  Subsumption          : 0.04
% 2.72/1.38  Abstraction          : 0.02
% 2.72/1.38  MUC search           : 0.00
% 2.72/1.38  Cooper               : 0.00
% 2.72/1.38  Total                : 0.64
% 2.72/1.38  Index Insertion      : 0.00
% 2.72/1.38  Index Deletion       : 0.00
% 2.72/1.38  Index Matching       : 0.00
% 2.72/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
