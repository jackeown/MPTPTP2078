%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:03 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 208 expanded)
%              Number of leaves         :   24 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 414 expanded)
%              Number of equality atoms :   41 ( 180 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_5] :
      ( k8_setfam_1(A_5,k1_xboole_0) = A_5
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_5] : k8_setfam_1(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_210,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k8_setfam_1(A_53,B_54),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_222,plain,(
    ! [A_5] :
      ( m1_subset_1(A_5,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_210])).

tff(c_228,plain,(
    ! [A_55] : m1_subset_1(A_55,k1_zfmisc_1(A_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_222])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_240,plain,(
    ! [A_55] : r1_tarski(A_55,A_55) ),
    inference(resolution,[status(thm)],[c_228,c_16])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_159,plain,(
    ! [A_48,B_49] :
      ( k6_setfam_1(A_48,B_49) = k1_setfam_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_176,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_159])).

tff(c_251,plain,(
    ! [A_57,B_58] :
      ( k8_setfam_1(A_57,B_58) = k6_setfam_1(A_57,B_58)
      | k1_xboole_0 = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_269,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_251])).

tff(c_280,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_269])).

tff(c_315,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_175,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_159])).

tff(c_266,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_251])).

tff(c_278,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_266])).

tff(c_314,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_329,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_314])).

tff(c_24,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_340,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_24])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_340])).

tff(c_350,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_359,plain,(
    ! [A_5] : k8_setfam_1(A_5,'#skF_2') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_32])).

tff(c_393,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_24])).

tff(c_459,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_393])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k8_setfam_1(A_7,B_8),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(A_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_463,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_12])).

tff(c_467,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_463])).

tff(c_484,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_467,c_16])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_484])).

tff(c_491,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_setfam_1(B_17),k1_setfam_1(A_16))
      | k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_492,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_493,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_491])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_518,plain,(
    ! [A_71] : k2_xboole_0(A_71,'#skF_3') = A_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_4])).

tff(c_71,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_71])).

tff(c_528,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_87])).

tff(c_542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_528])).

tff(c_543,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_490,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_545,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_24])).

tff(c_564,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_545])).

tff(c_567,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_564])).

tff(c_570,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_567])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.39  
% 2.33/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.40  %$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.40  
% 2.61/1.40  %Foreground sorts:
% 2.61/1.40  
% 2.61/1.40  
% 2.61/1.40  %Background operators:
% 2.61/1.40  
% 2.61/1.40  
% 2.61/1.40  %Foreground operators:
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.40  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.61/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.40  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.61/1.40  
% 2.61/1.41  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.61/1.41  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.61/1.41  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.61/1.41  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.61/1.41  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.61/1.41  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.61/1.41  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.61/1.41  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.61/1.41  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.61/1.41  tff(c_6, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.41  tff(c_8, plain, (![A_5]: (k8_setfam_1(A_5, k1_xboole_0)=A_5 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.61/1.41  tff(c_32, plain, (![A_5]: (k8_setfam_1(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.61/1.41  tff(c_210, plain, (![A_53, B_54]: (m1_subset_1(k8_setfam_1(A_53, B_54), k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.61/1.41  tff(c_222, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_210])).
% 2.61/1.41  tff(c_228, plain, (![A_55]: (m1_subset_1(A_55, k1_zfmisc_1(A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_222])).
% 2.61/1.41  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.61/1.41  tff(c_240, plain, (![A_55]: (r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_228, c_16])).
% 2.61/1.41  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.41  tff(c_159, plain, (![A_48, B_49]: (k6_setfam_1(A_48, B_49)=k1_setfam_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.61/1.41  tff(c_176, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_159])).
% 2.61/1.41  tff(c_251, plain, (![A_57, B_58]: (k8_setfam_1(A_57, B_58)=k6_setfam_1(A_57, B_58) | k1_xboole_0=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.61/1.41  tff(c_269, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28, c_251])).
% 2.61/1.41  tff(c_280, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_269])).
% 2.61/1.41  tff(c_315, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_280])).
% 2.61/1.41  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.41  tff(c_175, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_159])).
% 2.61/1.41  tff(c_266, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_251])).
% 2.61/1.41  tff(c_278, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_175, c_266])).
% 2.61/1.41  tff(c_314, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_278])).
% 2.61/1.41  tff(c_329, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_315, c_314])).
% 2.61/1.41  tff(c_24, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.41  tff(c_340, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_24])).
% 2.61/1.41  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_340])).
% 2.61/1.41  tff(c_350, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_280])).
% 2.61/1.41  tff(c_359, plain, (![A_5]: (k8_setfam_1(A_5, '#skF_2')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_314, c_32])).
% 2.61/1.41  tff(c_393, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_24])).
% 2.61/1.41  tff(c_459, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_393])).
% 2.61/1.41  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(k8_setfam_1(A_7, B_8), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(k1_zfmisc_1(A_7))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.61/1.41  tff(c_463, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_350, c_12])).
% 2.61/1.41  tff(c_467, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_463])).
% 2.61/1.41  tff(c_484, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_467, c_16])).
% 2.61/1.41  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_459, c_484])).
% 2.61/1.41  tff(c_491, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_278])).
% 2.61/1.41  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.41  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k1_setfam_1(B_17), k1_setfam_1(A_16)) | k1_xboole_0=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.41  tff(c_492, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_280])).
% 2.61/1.41  tff(c_493, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_492, c_491])).
% 2.61/1.41  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.41  tff(c_518, plain, (![A_71]: (k2_xboole_0(A_71, '#skF_3')=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_492, c_4])).
% 2.61/1.41  tff(c_71, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.41  tff(c_87, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_26, c_71])).
% 2.61/1.41  tff(c_528, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_518, c_87])).
% 2.61/1.41  tff(c_542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_493, c_528])).
% 2.61/1.41  tff(c_543, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_280])).
% 2.61/1.41  tff(c_490, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_278])).
% 2.61/1.41  tff(c_545, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_24])).
% 2.61/1.41  tff(c_564, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_545])).
% 2.61/1.41  tff(c_567, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_564])).
% 2.61/1.41  tff(c_570, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_567])).
% 2.61/1.41  tff(c_572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_491, c_570])).
% 2.61/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.41  
% 2.61/1.41  Inference rules
% 2.61/1.41  ----------------------
% 2.61/1.41  #Ref     : 0
% 2.61/1.41  #Sup     : 113
% 2.61/1.41  #Fact    : 0
% 2.61/1.41  #Define  : 0
% 2.61/1.41  #Split   : 3
% 2.61/1.41  #Chain   : 0
% 2.61/1.41  #Close   : 0
% 2.61/1.41  
% 2.61/1.41  Ordering : KBO
% 2.61/1.41  
% 2.61/1.41  Simplification rules
% 2.61/1.41  ----------------------
% 2.61/1.41  #Subsume      : 4
% 2.61/1.41  #Demod        : 78
% 2.61/1.41  #Tautology    : 76
% 2.61/1.41  #SimpNegUnit  : 3
% 2.61/1.41  #BackRed      : 42
% 2.61/1.41  
% 2.61/1.41  #Partial instantiations: 0
% 2.61/1.41  #Strategies tried      : 1
% 2.61/1.41  
% 2.61/1.41  Timing (in seconds)
% 2.61/1.41  ----------------------
% 2.61/1.41  Preprocessing        : 0.30
% 2.61/1.41  Parsing              : 0.16
% 2.61/1.41  CNF conversion       : 0.02
% 2.61/1.41  Main loop            : 0.28
% 2.61/1.41  Inferencing          : 0.10
% 2.61/1.41  Reduction            : 0.09
% 2.61/1.41  Demodulation         : 0.06
% 2.61/1.41  BG Simplification    : 0.02
% 2.61/1.41  Subsumption          : 0.05
% 2.61/1.41  Abstraction          : 0.02
% 2.61/1.41  MUC search           : 0.00
% 2.61/1.41  Cooper               : 0.00
% 2.61/1.41  Total                : 0.61
% 2.61/1.41  Index Insertion      : 0.00
% 2.61/1.41  Index Deletion       : 0.00
% 2.61/1.42  Index Matching       : 0.00
% 2.61/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
