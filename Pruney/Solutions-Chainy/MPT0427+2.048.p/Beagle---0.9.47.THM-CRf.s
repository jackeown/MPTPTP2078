%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:03 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 314 expanded)
%              Number of leaves         :   28 ( 112 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 640 expanded)
%              Number of equality atoms :   50 ( 292 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_12] :
      ( k8_setfam_1(A_12,k1_xboole_0) = A_12
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    ! [A_12] : k8_setfam_1(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_265,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1(k8_setfam_1(A_72,B_73),k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(A_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_277,plain,(
    ! [A_12] :
      ( m1_subset_1(A_12,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_265])).

tff(c_283,plain,(
    ! [A_74] : m1_subset_1(A_74,k1_zfmisc_1(A_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_277])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_295,plain,(
    ! [A_74] : r1_tarski(A_74,A_74) ),
    inference(resolution,[status(thm)],[c_283,c_26])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_169,plain,(
    ! [A_49,B_50] :
      ( k6_setfam_1(A_49,B_50) = k1_setfam_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_185,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_169])).

tff(c_318,plain,(
    ! [A_79,B_80] :
      ( k8_setfam_1(A_79,B_80) = k6_setfam_1(A_79,B_80)
      | k1_xboole_0 = B_80
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_333,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_318])).

tff(c_346,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_333])).

tff(c_352,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_186,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_169])).

tff(c_336,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_318])).

tff(c_348,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_336])).

tff(c_458,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_348])).

tff(c_459,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_458])).

tff(c_367,plain,(
    ! [A_12] : k8_setfam_1(A_12,'#skF_2') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_42])).

tff(c_463,plain,(
    ! [A_12] : k8_setfam_1(A_12,'#skF_3') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_367])).

tff(c_34,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_410,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_34])).

tff(c_486,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_410])).

tff(c_489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_486])).

tff(c_490,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_458])).

tff(c_492,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_410])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k8_setfam_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_496,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_22])).

tff(c_500,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_496])).

tff(c_512,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_500,c_26])).

tff(c_517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_492,c_512])).

tff(c_519,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_36,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_setfam_1(B_24),k1_setfam_1(A_23))
      | k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_550,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_552,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_519])).

tff(c_80,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_92,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_16,c_80])).

tff(c_99,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_99])).

tff(c_559,plain,(
    ! [A_11] : k4_xboole_0('#skF_3',A_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_550,c_118])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_165,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_xboole_0(A_46,C_47)
      | ~ r1_xboole_0(B_48,C_47)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_726,plain,(
    ! [A_105,B_106,A_107] :
      ( r1_xboole_0(A_105,B_106)
      | ~ r1_tarski(A_105,A_107)
      | k4_xboole_0(A_107,B_106) != A_107 ) ),
    inference(resolution,[status(thm)],[c_14,c_165])).

tff(c_738,plain,(
    ! [B_106] :
      ( r1_xboole_0('#skF_2',B_106)
      | k4_xboole_0('#skF_3',B_106) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_36,c_726])).

tff(c_747,plain,(
    ! [B_108] : r1_xboole_0('#skF_2',B_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_738])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_755,plain,(
    ! [B_109] : k4_xboole_0('#skF_2',B_109) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_747,c_12])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k2_xboole_0(A_4,B_5)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_565,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k2_xboole_0(A_4,B_5)) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_8])).

tff(c_760,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_565])).

tff(c_782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_552,c_760])).

tff(c_783,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_518,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_521,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_34])).

tff(c_785,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_521])).

tff(c_797,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_785])).

tff(c_803,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_797])).

tff(c_805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_519,c_803])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:19:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.41  
% 2.79/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.79/1.42  
% 2.79/1.42  %Foreground sorts:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Background operators:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Foreground operators:
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.79/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.42  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.79/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.79/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.42  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.79/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.79/1.42  
% 2.79/1.43  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.79/1.43  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.79/1.43  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.79/1.43  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.43  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.79/1.43  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.79/1.43  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.79/1.43  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.79/1.43  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.79/1.43  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.79/1.43  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.79/1.43  tff(c_16, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.79/1.43  tff(c_18, plain, (![A_12]: (k8_setfam_1(A_12, k1_xboole_0)=A_12 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.79/1.43  tff(c_42, plain, (![A_12]: (k8_setfam_1(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.79/1.43  tff(c_265, plain, (![A_72, B_73]: (m1_subset_1(k8_setfam_1(A_72, B_73), k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(A_72))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.43  tff(c_277, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(superposition, [status(thm), theory('equality')], [c_42, c_265])).
% 2.79/1.43  tff(c_283, plain, (![A_74]: (m1_subset_1(A_74, k1_zfmisc_1(A_74)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_277])).
% 2.79/1.43  tff(c_26, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.43  tff(c_295, plain, (![A_74]: (r1_tarski(A_74, A_74))), inference(resolution, [status(thm)], [c_283, c_26])).
% 2.79/1.43  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.79/1.43  tff(c_169, plain, (![A_49, B_50]: (k6_setfam_1(A_49, B_50)=k1_setfam_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.79/1.43  tff(c_185, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_40, c_169])).
% 2.79/1.43  tff(c_318, plain, (![A_79, B_80]: (k8_setfam_1(A_79, B_80)=k6_setfam_1(A_79, B_80) | k1_xboole_0=B_80 | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.79/1.43  tff(c_333, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_40, c_318])).
% 2.79/1.43  tff(c_346, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_333])).
% 2.79/1.43  tff(c_352, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_346])).
% 2.79/1.43  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.79/1.43  tff(c_186, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_169])).
% 2.79/1.43  tff(c_336, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_318])).
% 2.79/1.43  tff(c_348, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_186, c_336])).
% 2.79/1.43  tff(c_458, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_352, c_348])).
% 2.79/1.43  tff(c_459, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_458])).
% 2.79/1.43  tff(c_367, plain, (![A_12]: (k8_setfam_1(A_12, '#skF_2')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_352, c_42])).
% 2.79/1.43  tff(c_463, plain, (![A_12]: (k8_setfam_1(A_12, '#skF_3')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_459, c_367])).
% 2.79/1.43  tff(c_34, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.79/1.43  tff(c_410, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_367, c_34])).
% 2.79/1.43  tff(c_486, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_463, c_410])).
% 2.79/1.43  tff(c_489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_295, c_486])).
% 2.79/1.43  tff(c_490, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_458])).
% 2.79/1.43  tff(c_492, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_410])).
% 2.79/1.43  tff(c_22, plain, (![A_14, B_15]: (m1_subset_1(k8_setfam_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.43  tff(c_496, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_490, c_22])).
% 2.79/1.43  tff(c_500, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_496])).
% 2.79/1.43  tff(c_512, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_500, c_26])).
% 2.79/1.43  tff(c_517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_492, c_512])).
% 2.79/1.43  tff(c_519, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_346])).
% 2.79/1.43  tff(c_36, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.79/1.43  tff(c_32, plain, (![B_24, A_23]: (r1_tarski(k1_setfam_1(B_24), k1_setfam_1(A_23)) | k1_xboole_0=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.79/1.43  tff(c_550, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_348])).
% 2.79/1.43  tff(c_552, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_550, c_519])).
% 2.79/1.43  tff(c_80, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.43  tff(c_92, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_16, c_80])).
% 2.79/1.43  tff(c_99, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.43  tff(c_118, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_92, c_99])).
% 2.79/1.43  tff(c_559, plain, (![A_11]: (k4_xboole_0('#skF_3', A_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_550, c_550, c_118])).
% 2.79/1.43  tff(c_14, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.43  tff(c_165, plain, (![A_46, C_47, B_48]: (r1_xboole_0(A_46, C_47) | ~r1_xboole_0(B_48, C_47) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.79/1.43  tff(c_726, plain, (![A_105, B_106, A_107]: (r1_xboole_0(A_105, B_106) | ~r1_tarski(A_105, A_107) | k4_xboole_0(A_107, B_106)!=A_107)), inference(resolution, [status(thm)], [c_14, c_165])).
% 2.79/1.43  tff(c_738, plain, (![B_106]: (r1_xboole_0('#skF_2', B_106) | k4_xboole_0('#skF_3', B_106)!='#skF_3')), inference(resolution, [status(thm)], [c_36, c_726])).
% 2.79/1.43  tff(c_747, plain, (![B_108]: (r1_xboole_0('#skF_2', B_108))), inference(demodulation, [status(thm), theory('equality')], [c_559, c_738])).
% 2.79/1.43  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.43  tff(c_755, plain, (![B_109]: (k4_xboole_0('#skF_2', B_109)='#skF_2')), inference(resolution, [status(thm)], [c_747, c_12])).
% 2.79/1.43  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k2_xboole_0(A_4, B_5))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.43  tff(c_565, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k2_xboole_0(A_4, B_5))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_550, c_8])).
% 2.79/1.43  tff(c_760, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_755, c_565])).
% 2.79/1.43  tff(c_782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_552, c_760])).
% 2.79/1.43  tff(c_783, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_348])).
% 2.79/1.43  tff(c_518, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_346])).
% 2.79/1.43  tff(c_521, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_34])).
% 2.79/1.43  tff(c_785, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_783, c_521])).
% 2.79/1.43  tff(c_797, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_785])).
% 2.79/1.43  tff(c_803, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_797])).
% 2.79/1.43  tff(c_805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_519, c_803])).
% 2.79/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  Inference rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Ref     : 0
% 2.79/1.43  #Sup     : 176
% 2.79/1.43  #Fact    : 0
% 2.79/1.43  #Define  : 0
% 2.79/1.43  #Split   : 3
% 2.79/1.43  #Chain   : 0
% 2.79/1.43  #Close   : 0
% 2.79/1.43  
% 2.79/1.43  Ordering : KBO
% 2.79/1.43  
% 2.79/1.43  Simplification rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Subsume      : 8
% 2.79/1.43  #Demod        : 110
% 2.79/1.43  #Tautology    : 118
% 2.79/1.43  #SimpNegUnit  : 3
% 2.79/1.43  #BackRed      : 53
% 2.79/1.43  
% 2.79/1.43  #Partial instantiations: 0
% 2.79/1.43  #Strategies tried      : 1
% 2.79/1.43  
% 2.79/1.43  Timing (in seconds)
% 2.79/1.43  ----------------------
% 2.79/1.44  Preprocessing        : 0.32
% 2.79/1.44  Parsing              : 0.17
% 2.79/1.44  CNF conversion       : 0.02
% 2.79/1.44  Main loop            : 0.35
% 2.79/1.44  Inferencing          : 0.13
% 2.79/1.44  Reduction            : 0.11
% 2.79/1.44  Demodulation         : 0.08
% 2.79/1.44  BG Simplification    : 0.02
% 2.79/1.44  Subsumption          : 0.06
% 2.79/1.44  Abstraction          : 0.02
% 2.79/1.44  MUC search           : 0.00
% 2.79/1.44  Cooper               : 0.00
% 2.79/1.44  Total                : 0.71
% 2.79/1.44  Index Insertion      : 0.00
% 2.79/1.44  Index Deletion       : 0.00
% 2.79/1.44  Index Matching       : 0.00
% 2.79/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
