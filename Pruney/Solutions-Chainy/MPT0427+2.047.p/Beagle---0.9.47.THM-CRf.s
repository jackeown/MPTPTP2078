%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:02 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 557 expanded)
%              Number of leaves         :   28 ( 190 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 (1204 expanded)
%              Number of equality atoms :   63 ( 572 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k1_enumset1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_53,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_61,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_152,plain,(
    ! [A_42,B_43] :
      ( k6_setfam_1(A_42,B_43) = k1_setfam_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_164,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_152])).

tff(c_253,plain,(
    ! [A_54,B_55] :
      ( k8_setfam_1(A_54,B_55) = k6_setfam_1(A_54,B_55)
      | k1_xboole_0 = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_264,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_253])).

tff(c_271,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_264])).

tff(c_274,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_165,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_152])).

tff(c_267,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_253])).

tff(c_273,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_267])).

tff(c_341,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_273])).

tff(c_342,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_141,plain,(
    ! [A_39] :
      ( k8_setfam_1(A_39,k1_xboole_0) = A_39
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_145,plain,(
    ! [A_39] :
      ( k8_setfam_1(A_39,k1_xboole_0) = A_39
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_26,c_141])).

tff(c_281,plain,(
    ! [A_39] :
      ( k8_setfam_1(A_39,'#skF_2') = A_39
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(A_39)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_274,c_145])).

tff(c_448,plain,(
    ! [A_66] :
      ( k8_setfam_1(A_66,'#skF_3') = A_66
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_66)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_342,c_281])).

tff(c_456,plain,(
    k8_setfam_1('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_61,c_448])).

tff(c_30,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_353,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_30])).

tff(c_459,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_353])).

tff(c_212,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k8_setfam_1(A_50,B_51),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_222,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k8_setfam_1(A_52,B_53),A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(resolution,[status(thm)],[c_212,c_24])).

tff(c_236,plain,(
    r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_222])).

tff(c_460,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_236])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_460])).

tff(c_486,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_244,plain,(
    k4_xboole_0(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_236,c_4])).

tff(c_276,plain,(
    k4_xboole_0(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_244])).

tff(c_489,plain,(
    k4_xboole_0(k1_setfam_1('#skF_3'),'#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_276])).

tff(c_14,plain,(
    ! [A_9] :
      ( k8_setfam_1(A_9,k1_xboole_0) = A_9
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_554,plain,(
    ! [A_72] :
      ( k8_setfam_1(A_72,'#skF_2') = A_72
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(A_72))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_274,c_14])).

tff(c_562,plain,(
    k8_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_554])).

tff(c_101,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    k4_xboole_0(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_30])).

tff(c_283,plain,(
    k4_xboole_0(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_109])).

tff(c_488,plain,(
    k4_xboole_0(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_283])).

tff(c_564,plain,(
    k4_xboole_0(k1_setfam_1('#skF_3'),'#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_488])).

tff(c_569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_564])).

tff(c_571,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_32,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_setfam_1(B_20),k1_setfam_1(A_19))
      | k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_603,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_606,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_571])).

tff(c_71,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_618,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_83])).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_119,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_119])).

tff(c_131,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_128])).

tff(c_614,plain,(
    ! [A_5] : k4_xboole_0(A_5,'#skF_3') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_131])).

tff(c_638,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_614])).

tff(c_645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_606,c_638])).

tff(c_646,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_570,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_575,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_30])).

tff(c_649,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_575])).

tff(c_667,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_649])).

tff(c_673,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_667])).

tff(c_675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_571,c_673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:26:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.42  
% 2.48/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.42  %$ r1_tarski > m1_subset_1 > k1_enumset1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.48/1.42  
% 2.48/1.42  %Foreground sorts:
% 2.48/1.42  
% 2.48/1.42  
% 2.48/1.42  %Background operators:
% 2.48/1.42  
% 2.48/1.42  
% 2.48/1.42  %Foreground operators:
% 2.48/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.42  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.48/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.48/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.42  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.48/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.48/1.42  
% 2.86/1.44  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.86/1.44  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.86/1.44  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.86/1.44  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.86/1.44  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.86/1.44  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.86/1.44  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.86/1.44  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.86/1.44  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.86/1.44  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.86/1.44  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.44  tff(c_53, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.86/1.44  tff(c_61, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_53])).
% 2.86/1.44  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.44  tff(c_152, plain, (![A_42, B_43]: (k6_setfam_1(A_42, B_43)=k1_setfam_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.86/1.44  tff(c_164, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_152])).
% 2.86/1.44  tff(c_253, plain, (![A_54, B_55]: (k8_setfam_1(A_54, B_55)=k6_setfam_1(A_54, B_55) | k1_xboole_0=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.86/1.44  tff(c_264, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_253])).
% 2.86/1.44  tff(c_271, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_164, c_264])).
% 2.86/1.44  tff(c_274, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_271])).
% 2.86/1.44  tff(c_165, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_152])).
% 2.86/1.44  tff(c_267, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_253])).
% 2.86/1.44  tff(c_273, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_267])).
% 2.86/1.44  tff(c_341, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_274, c_273])).
% 2.86/1.44  tff(c_342, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_341])).
% 2.86/1.44  tff(c_26, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.86/1.44  tff(c_141, plain, (![A_39]: (k8_setfam_1(A_39, k1_xboole_0)=A_39 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_39))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.86/1.44  tff(c_145, plain, (![A_39]: (k8_setfam_1(A_39, k1_xboole_0)=A_39 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_39)))), inference(resolution, [status(thm)], [c_26, c_141])).
% 2.86/1.44  tff(c_281, plain, (![A_39]: (k8_setfam_1(A_39, '#skF_2')=A_39 | ~r1_tarski('#skF_2', k1_zfmisc_1(A_39)))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_274, c_145])).
% 2.86/1.44  tff(c_448, plain, (![A_66]: (k8_setfam_1(A_66, '#skF_3')=A_66 | ~r1_tarski('#skF_3', k1_zfmisc_1(A_66)))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_342, c_281])).
% 2.86/1.44  tff(c_456, plain, (k8_setfam_1('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_61, c_448])).
% 2.86/1.44  tff(c_30, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.44  tff(c_353, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_30])).
% 2.86/1.44  tff(c_459, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_456, c_353])).
% 2.86/1.44  tff(c_212, plain, (![A_50, B_51]: (m1_subset_1(k8_setfam_1(A_50, B_51), k1_zfmisc_1(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_50))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.44  tff(c_24, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.86/1.44  tff(c_222, plain, (![A_52, B_53]: (r1_tarski(k8_setfam_1(A_52, B_53), A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(resolution, [status(thm)], [c_212, c_24])).
% 2.86/1.44  tff(c_236, plain, (r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_34, c_222])).
% 2.86/1.44  tff(c_460, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_236])).
% 2.86/1.44  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_459, c_460])).
% 2.86/1.44  tff(c_486, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_341])).
% 2.86/1.44  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.44  tff(c_244, plain, (k4_xboole_0(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_236, c_4])).
% 2.86/1.44  tff(c_276, plain, (k4_xboole_0(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_274, c_244])).
% 2.86/1.44  tff(c_489, plain, (k4_xboole_0(k1_setfam_1('#skF_3'), '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_486, c_276])).
% 2.86/1.44  tff(c_14, plain, (![A_9]: (k8_setfam_1(A_9, k1_xboole_0)=A_9 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.86/1.44  tff(c_554, plain, (![A_72]: (k8_setfam_1(A_72, '#skF_2')=A_72 | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(A_72))))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_274, c_14])).
% 2.86/1.44  tff(c_562, plain, (k8_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_36, c_554])).
% 2.86/1.44  tff(c_101, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | k4_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.44  tff(c_109, plain, (k4_xboole_0(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_101, c_30])).
% 2.86/1.44  tff(c_283, plain, (k4_xboole_0(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_274, c_109])).
% 2.86/1.44  tff(c_488, plain, (k4_xboole_0(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_486, c_283])).
% 2.86/1.44  tff(c_564, plain, (k4_xboole_0(k1_setfam_1('#skF_3'), '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_562, c_488])).
% 2.86/1.44  tff(c_569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_489, c_564])).
% 2.86/1.44  tff(c_571, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_271])).
% 2.86/1.44  tff(c_32, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.44  tff(c_28, plain, (![B_20, A_19]: (r1_tarski(k1_setfam_1(B_20), k1_setfam_1(A_19)) | k1_xboole_0=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.86/1.44  tff(c_603, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_273])).
% 2.86/1.44  tff(c_606, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_603, c_571])).
% 2.86/1.44  tff(c_71, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.44  tff(c_83, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_71])).
% 2.86/1.44  tff(c_618, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_603, c_83])).
% 2.86/1.44  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.86/1.44  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.44  tff(c_119, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.44  tff(c_128, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_119])).
% 2.86/1.44  tff(c_131, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_128])).
% 2.86/1.44  tff(c_614, plain, (![A_5]: (k4_xboole_0(A_5, '#skF_3')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_603, c_131])).
% 2.86/1.44  tff(c_638, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_618, c_614])).
% 2.86/1.44  tff(c_645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_606, c_638])).
% 2.86/1.44  tff(c_646, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_273])).
% 2.86/1.44  tff(c_570, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_271])).
% 2.86/1.44  tff(c_575, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_570, c_30])).
% 2.86/1.44  tff(c_649, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_646, c_575])).
% 2.86/1.44  tff(c_667, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_649])).
% 2.86/1.44  tff(c_673, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_667])).
% 2.86/1.44  tff(c_675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_571, c_673])).
% 2.86/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.44  
% 2.86/1.44  Inference rules
% 2.86/1.44  ----------------------
% 2.86/1.44  #Ref     : 0
% 2.86/1.44  #Sup     : 148
% 2.86/1.44  #Fact    : 0
% 2.86/1.44  #Define  : 0
% 2.86/1.44  #Split   : 3
% 2.86/1.44  #Chain   : 0
% 2.86/1.44  #Close   : 0
% 2.86/1.44  
% 2.86/1.44  Ordering : KBO
% 2.86/1.44  
% 2.86/1.44  Simplification rules
% 2.86/1.44  ----------------------
% 2.86/1.44  #Subsume      : 2
% 2.86/1.44  #Demod        : 132
% 2.86/1.44  #Tautology    : 106
% 2.86/1.44  #SimpNegUnit  : 3
% 2.86/1.44  #BackRed      : 69
% 2.86/1.44  
% 2.86/1.44  #Partial instantiations: 0
% 2.86/1.44  #Strategies tried      : 1
% 2.86/1.44  
% 2.86/1.44  Timing (in seconds)
% 2.86/1.44  ----------------------
% 2.86/1.44  Preprocessing        : 0.32
% 2.86/1.44  Parsing              : 0.17
% 2.86/1.44  CNF conversion       : 0.02
% 2.86/1.44  Main loop            : 0.30
% 2.86/1.44  Inferencing          : 0.11
% 2.86/1.45  Reduction            : 0.10
% 2.86/1.45  Demodulation         : 0.07
% 2.86/1.45  BG Simplification    : 0.02
% 2.86/1.45  Subsumption          : 0.04
% 2.86/1.45  Abstraction          : 0.02
% 2.86/1.45  MUC search           : 0.00
% 2.86/1.45  Cooper               : 0.00
% 2.86/1.45  Total                : 0.66
% 2.86/1.45  Index Insertion      : 0.00
% 2.86/1.45  Index Deletion       : 0.00
% 2.86/1.45  Index Matching       : 0.00
% 2.86/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
