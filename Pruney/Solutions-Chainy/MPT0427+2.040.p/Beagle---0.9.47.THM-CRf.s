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
% DateTime   : Thu Dec  3 09:58:01 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 288 expanded)
%              Number of leaves         :   26 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 588 expanded)
%              Number of equality atoms :   44 ( 271 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_7] :
      ( k8_setfam_1(A_7,k1_xboole_0) = A_7
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ! [A_7] : k8_setfam_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_219,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k8_setfam_1(A_60,B_61),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_231,plain,(
    ! [A_7] :
      ( m1_subset_1(A_7,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_7))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_219])).

tff(c_237,plain,(
    ! [A_62] : m1_subset_1(A_62,k1_zfmisc_1(A_62)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_231])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_249,plain,(
    ! [A_62] : r1_tarski(A_62,A_62) ),
    inference(resolution,[status(thm)],[c_237,c_20])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_128,plain,(
    ! [A_37,B_38] :
      ( k6_setfam_1(A_37,B_38) = k1_setfam_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(A_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_144,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_289,plain,(
    ! [A_65,B_66] :
      ( k8_setfam_1(A_65,B_66) = k6_setfam_1(A_65,B_66)
      | k1_xboole_0 = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_304,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_289])).

tff(c_316,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_304])).

tff(c_323,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_145,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_128])).

tff(c_307,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_289])).

tff(c_318,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_307])).

tff(c_439,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_318])).

tff(c_440,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_334,plain,(
    ! [A_7] : k8_setfam_1(A_7,'#skF_2') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_36])).

tff(c_444,plain,(
    ! [A_7] : k8_setfam_1(A_7,'#skF_3') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_334])).

tff(c_28,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_385,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_28])).

tff(c_506,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_385])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_506])).

tff(c_510,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_512,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_385])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k8_setfam_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_516,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_16])).

tff(c_520,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_516])).

tff(c_526,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_520,c_20])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_512,c_526])).

tff(c_533,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_setfam_1(B_19),k1_setfam_1(A_18))
      | k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_532,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_534,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_535,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_533])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_107,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_540,plain,(
    ! [A_5] : k3_xboole_0(A_5,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_534,c_107])).

tff(c_62,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_62])).

tff(c_593,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_78])).

tff(c_595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_535,c_593])).

tff(c_596,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_598,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_28])).

tff(c_608,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_598])).

tff(c_620,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_608])).

tff(c_623,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_620])).

tff(c_625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:41:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.39  
% 2.67/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.67/1.40  
% 2.67/1.40  %Foreground sorts:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Background operators:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Foreground operators:
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.40  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.67/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.40  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.67/1.40  
% 2.67/1.41  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.67/1.41  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.67/1.41  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.67/1.41  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.67/1.41  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.67/1.41  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.67/1.41  tff(f_72, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.67/1.41  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.67/1.41  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.67/1.41  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.67/1.41  tff(c_10, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.41  tff(c_12, plain, (![A_7]: (k8_setfam_1(A_7, k1_xboole_0)=A_7 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_7))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.41  tff(c_36, plain, (![A_7]: (k8_setfam_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.67/1.41  tff(c_219, plain, (![A_60, B_61]: (m1_subset_1(k8_setfam_1(A_60, B_61), k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.67/1.41  tff(c_231, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_7))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_219])).
% 2.67/1.41  tff(c_237, plain, (![A_62]: (m1_subset_1(A_62, k1_zfmisc_1(A_62)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_231])).
% 2.67/1.41  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.41  tff(c_249, plain, (![A_62]: (r1_tarski(A_62, A_62))), inference(resolution, [status(thm)], [c_237, c_20])).
% 2.67/1.41  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.41  tff(c_128, plain, (![A_37, B_38]: (k6_setfam_1(A_37, B_38)=k1_setfam_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(k1_zfmisc_1(A_37))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.67/1.41  tff(c_144, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_128])).
% 2.67/1.41  tff(c_289, plain, (![A_65, B_66]: (k8_setfam_1(A_65, B_66)=k6_setfam_1(A_65, B_66) | k1_xboole_0=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.41  tff(c_304, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_34, c_289])).
% 2.67/1.41  tff(c_316, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_304])).
% 2.67/1.41  tff(c_323, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_316])).
% 2.67/1.41  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.41  tff(c_145, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_128])).
% 2.67/1.41  tff(c_307, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_32, c_289])).
% 2.67/1.41  tff(c_318, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_307])).
% 2.67/1.41  tff(c_439, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_323, c_318])).
% 2.67/1.41  tff(c_440, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_439])).
% 2.67/1.41  tff(c_334, plain, (![A_7]: (k8_setfam_1(A_7, '#skF_2')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_323, c_36])).
% 2.67/1.41  tff(c_444, plain, (![A_7]: (k8_setfam_1(A_7, '#skF_3')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_440, c_334])).
% 2.67/1.41  tff(c_28, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.41  tff(c_385, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_334, c_28])).
% 2.67/1.41  tff(c_506, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_385])).
% 2.67/1.41  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_506])).
% 2.67/1.41  tff(c_510, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_439])).
% 2.67/1.41  tff(c_512, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_510, c_385])).
% 2.67/1.41  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(k8_setfam_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.67/1.41  tff(c_516, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_510, c_16])).
% 2.67/1.41  tff(c_520, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_516])).
% 2.67/1.41  tff(c_526, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_520, c_20])).
% 2.67/1.41  tff(c_531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_512, c_526])).
% 2.67/1.41  tff(c_533, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_316])).
% 2.67/1.41  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.41  tff(c_26, plain, (![B_19, A_18]: (r1_tarski(k1_setfam_1(B_19), k1_setfam_1(A_18)) | k1_xboole_0=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.41  tff(c_532, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_316])).
% 2.67/1.41  tff(c_534, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_318])).
% 2.67/1.41  tff(c_535, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_534, c_533])).
% 2.67/1.41  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.41  tff(c_99, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.41  tff(c_107, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_99])).
% 2.67/1.41  tff(c_540, plain, (![A_5]: (k3_xboole_0(A_5, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_534, c_534, c_107])).
% 2.67/1.41  tff(c_62, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.41  tff(c_78, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_30, c_62])).
% 2.67/1.41  tff(c_593, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_540, c_78])).
% 2.67/1.41  tff(c_595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_535, c_593])).
% 2.67/1.41  tff(c_596, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_318])).
% 2.67/1.41  tff(c_598, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_596, c_28])).
% 2.67/1.41  tff(c_608, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_532, c_598])).
% 2.67/1.41  tff(c_620, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_608])).
% 2.67/1.41  tff(c_623, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_620])).
% 2.67/1.41  tff(c_625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_533, c_623])).
% 2.67/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.41  
% 2.67/1.41  Inference rules
% 2.67/1.41  ----------------------
% 2.67/1.41  #Ref     : 0
% 2.67/1.41  #Sup     : 124
% 2.67/1.41  #Fact    : 0
% 2.67/1.41  #Define  : 0
% 2.67/1.41  #Split   : 3
% 2.67/1.41  #Chain   : 0
% 2.67/1.41  #Close   : 0
% 2.67/1.41  
% 2.67/1.41  Ordering : KBO
% 2.67/1.41  
% 2.67/1.41  Simplification rules
% 2.67/1.41  ----------------------
% 2.67/1.41  #Subsume      : 5
% 2.67/1.41  #Demod        : 87
% 2.67/1.41  #Tautology    : 84
% 2.67/1.41  #SimpNegUnit  : 3
% 2.67/1.41  #BackRed      : 43
% 2.67/1.41  
% 2.67/1.41  #Partial instantiations: 0
% 2.67/1.41  #Strategies tried      : 1
% 2.67/1.41  
% 2.67/1.41  Timing (in seconds)
% 2.67/1.41  ----------------------
% 2.67/1.41  Preprocessing        : 0.33
% 2.67/1.41  Parsing              : 0.18
% 2.67/1.41  CNF conversion       : 0.02
% 2.67/1.41  Main loop            : 0.28
% 2.67/1.41  Inferencing          : 0.10
% 2.67/1.41  Reduction            : 0.09
% 2.67/1.41  Demodulation         : 0.07
% 2.67/1.42  BG Simplification    : 0.02
% 2.67/1.42  Subsumption          : 0.05
% 2.67/1.42  Abstraction          : 0.02
% 2.67/1.42  MUC search           : 0.00
% 2.67/1.42  Cooper               : 0.00
% 2.67/1.42  Total                : 0.65
% 2.67/1.42  Index Insertion      : 0.00
% 2.67/1.42  Index Deletion       : 0.00
% 2.67/1.42  Index Matching       : 0.00
% 2.67/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
