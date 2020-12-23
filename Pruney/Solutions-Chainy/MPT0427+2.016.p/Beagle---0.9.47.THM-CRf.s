%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:58 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 240 expanded)
%              Number of leaves         :   25 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 483 expanded)
%              Number of equality atoms :   44 ( 217 expanded)
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

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_7] :
      ( k8_setfam_1(A_7,k1_xboole_0) = A_7
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [A_7] : k8_setfam_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_288,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k8_setfam_1(A_48,B_49),k1_zfmisc_1(A_48))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_300,plain,(
    ! [A_7] :
      ( m1_subset_1(A_7,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_7))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_288])).

tff(c_306,plain,(
    ! [A_50] : m1_subset_1(A_50,k1_zfmisc_1(A_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_300])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_318,plain,(
    ! [A_50] : r1_tarski(A_50,A_50) ),
    inference(resolution,[status(thm)],[c_306,c_18])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_209,plain,(
    ! [A_34,B_35] :
      ( k6_setfam_1(A_34,B_35) = k1_setfam_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_225,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_209])).

tff(c_379,plain,(
    ! [A_61,B_62] :
      ( k8_setfam_1(A_61,B_62) = k6_setfam_1(A_61,B_62)
      | k1_xboole_0 = B_62
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_394,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_379])).

tff(c_407,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_394])).

tff(c_413,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_407])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_226,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_209])).

tff(c_397,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_379])).

tff(c_409,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_397])).

tff(c_439,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_409])).

tff(c_440,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_26,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_449,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_26])).

tff(c_457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_449])).

tff(c_458,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_421,plain,(
    ! [A_7] : k8_setfam_1(A_7,'#skF_2') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_34])).

tff(c_510,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_26])).

tff(c_584,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_510])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k8_setfam_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_528,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_14])).

tff(c_532,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_528])).

tff(c_602,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_532,c_18])).

tff(c_607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_584,c_602])).

tff(c_609,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_setfam_1(B_19),k1_setfam_1(A_18))
      | k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_652,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_653,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_609])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_695,plain,(
    ! [A_75] : k2_xboole_0('#skF_3',A_75) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_86])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_79])).

tff(c_124,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_705,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_124])).

tff(c_733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_653,c_705])).

tff(c_734,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_608,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_610,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_26])).

tff(c_736,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_610])).

tff(c_748,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_736])).

tff(c_751,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_748])).

tff(c_753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_609,c_751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:51:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.77/1.44  
% 2.77/1.44  %Foreground sorts:
% 2.77/1.44  
% 2.77/1.44  
% 2.77/1.44  %Background operators:
% 2.77/1.44  
% 2.77/1.44  
% 2.77/1.44  %Foreground operators:
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.44  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.77/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.44  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.77/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.77/1.44  
% 2.77/1.46  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.77/1.46  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.77/1.46  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.77/1.46  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.77/1.46  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.77/1.46  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.77/1.46  tff(f_70, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.77/1.46  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.77/1.46  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.77/1.46  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.77/1.46  tff(c_8, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.46  tff(c_10, plain, (![A_7]: (k8_setfam_1(A_7, k1_xboole_0)=A_7 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_7))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.77/1.46  tff(c_34, plain, (![A_7]: (k8_setfam_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.77/1.46  tff(c_288, plain, (![A_48, B_49]: (m1_subset_1(k8_setfam_1(A_48, B_49), k1_zfmisc_1(A_48)) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.77/1.46  tff(c_300, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_7))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_288])).
% 2.77/1.46  tff(c_306, plain, (![A_50]: (m1_subset_1(A_50, k1_zfmisc_1(A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_300])).
% 2.77/1.46  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.77/1.46  tff(c_318, plain, (![A_50]: (r1_tarski(A_50, A_50))), inference(resolution, [status(thm)], [c_306, c_18])).
% 2.77/1.46  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.46  tff(c_209, plain, (![A_34, B_35]: (k6_setfam_1(A_34, B_35)=k1_setfam_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.77/1.46  tff(c_225, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_209])).
% 2.77/1.46  tff(c_379, plain, (![A_61, B_62]: (k8_setfam_1(A_61, B_62)=k6_setfam_1(A_61, B_62) | k1_xboole_0=B_62 | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.77/1.46  tff(c_394, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_379])).
% 2.77/1.46  tff(c_407, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_225, c_394])).
% 2.77/1.46  tff(c_413, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_407])).
% 2.77/1.46  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.46  tff(c_226, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_209])).
% 2.77/1.46  tff(c_397, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_379])).
% 2.77/1.46  tff(c_409, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_397])).
% 2.77/1.46  tff(c_439, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_413, c_409])).
% 2.77/1.46  tff(c_440, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_439])).
% 2.77/1.46  tff(c_26, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.46  tff(c_449, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_26])).
% 2.77/1.46  tff(c_457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_449])).
% 2.77/1.46  tff(c_458, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_439])).
% 2.77/1.46  tff(c_421, plain, (![A_7]: (k8_setfam_1(A_7, '#skF_2')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_413, c_34])).
% 2.77/1.46  tff(c_510, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_421, c_26])).
% 2.77/1.46  tff(c_584, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_510])).
% 2.77/1.46  tff(c_14, plain, (![A_9, B_10]: (m1_subset_1(k8_setfam_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.77/1.46  tff(c_528, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_458, c_14])).
% 2.77/1.46  tff(c_532, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_528])).
% 2.77/1.46  tff(c_602, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_532, c_18])).
% 2.77/1.46  tff(c_607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_584, c_602])).
% 2.77/1.46  tff(c_609, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_407])).
% 2.77/1.46  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.46  tff(c_24, plain, (![B_19, A_18]: (r1_tarski(k1_setfam_1(B_19), k1_setfam_1(A_18)) | k1_xboole_0=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.77/1.46  tff(c_652, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_409])).
% 2.77/1.46  tff(c_653, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_652, c_609])).
% 2.77/1.46  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.77/1.46  tff(c_79, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.46  tff(c_86, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_79])).
% 2.77/1.46  tff(c_695, plain, (![A_75]: (k2_xboole_0('#skF_3', A_75)=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_652, c_86])).
% 2.77/1.46  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.46  tff(c_87, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_79])).
% 2.77/1.46  tff(c_124, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_87])).
% 2.77/1.46  tff(c_705, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_695, c_124])).
% 2.77/1.46  tff(c_733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_653, c_705])).
% 2.77/1.46  tff(c_734, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_409])).
% 2.77/1.46  tff(c_608, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_407])).
% 2.77/1.46  tff(c_610, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_26])).
% 2.77/1.46  tff(c_736, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_734, c_610])).
% 2.77/1.46  tff(c_748, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_736])).
% 2.77/1.46  tff(c_751, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_748])).
% 2.77/1.46  tff(c_753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_609, c_751])).
% 2.77/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.46  
% 2.77/1.46  Inference rules
% 2.77/1.46  ----------------------
% 2.77/1.46  #Ref     : 0
% 2.77/1.46  #Sup     : 159
% 2.77/1.46  #Fact    : 0
% 2.77/1.46  #Define  : 0
% 2.77/1.46  #Split   : 3
% 2.77/1.46  #Chain   : 0
% 2.77/1.46  #Close   : 0
% 2.77/1.46  
% 2.77/1.46  Ordering : KBO
% 2.77/1.46  
% 2.77/1.46  Simplification rules
% 2.77/1.46  ----------------------
% 2.77/1.46  #Subsume      : 3
% 2.77/1.46  #Demod        : 93
% 2.77/1.46  #Tautology    : 113
% 2.77/1.46  #SimpNegUnit  : 3
% 2.77/1.46  #BackRed      : 32
% 2.77/1.46  
% 2.77/1.46  #Partial instantiations: 0
% 2.77/1.46  #Strategies tried      : 1
% 2.77/1.46  
% 2.77/1.46  Timing (in seconds)
% 2.77/1.46  ----------------------
% 2.77/1.46  Preprocessing        : 0.30
% 2.77/1.46  Parsing              : 0.16
% 2.77/1.46  CNF conversion       : 0.02
% 2.77/1.46  Main loop            : 0.38
% 2.77/1.46  Inferencing          : 0.15
% 2.77/1.46  Reduction            : 0.12
% 2.77/1.46  Demodulation         : 0.09
% 2.77/1.46  BG Simplification    : 0.02
% 2.77/1.46  Subsumption          : 0.06
% 2.77/1.46  Abstraction          : 0.02
% 2.77/1.46  MUC search           : 0.00
% 2.77/1.46  Cooper               : 0.00
% 2.77/1.46  Total                : 0.72
% 2.77/1.46  Index Insertion      : 0.00
% 2.77/1.46  Index Deletion       : 0.00
% 2.77/1.46  Index Matching       : 0.00
% 2.77/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
