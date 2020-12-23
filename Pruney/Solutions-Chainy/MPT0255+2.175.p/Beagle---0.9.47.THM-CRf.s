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
% DateTime   : Thu Dec  3 09:52:00 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 258 expanded)
%              Number of leaves         :   35 ( 102 expanded)
%              Depth                    :   15
%              Number of atoms          :   56 ( 274 expanded)
%              Number of equality atoms :   49 ( 183 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_75,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_48,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_50,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_123,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_137,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_8])).

tff(c_154,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_163,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_154])).

tff(c_169,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_163])).

tff(c_183,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_14])).

tff(c_190,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_183,c_8])).

tff(c_18,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_198,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_18])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_282,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_291,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_282])).

tff(c_294,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_291])).

tff(c_44,plain,(
    ! [B_67] : k4_xboole_0(k1_tarski(B_67),k1_tarski(B_67)) != k1_tarski(B_67) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_295,plain,(
    ! [B_67] : k1_tarski(B_67) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_44])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_196,plain,(
    ! [A_8] : k4_xboole_0('#skF_1',A_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_190,c_10])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_395,plain,(
    ! [A_100,B_101] : k5_xboole_0(k5_xboole_0(A_100,B_101),k2_xboole_0(A_100,B_101)) = k3_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_438,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_395])).

tff(c_443,plain,(
    ! [A_102] : k5_xboole_0('#skF_1',A_102) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_4,c_438])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_456,plain,(
    ! [B_6] : k4_xboole_0('#skF_1',B_6) = k3_xboole_0('#skF_1',B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_6])).

tff(c_482,plain,(
    ! [B_6] : k3_xboole_0('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_456])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_197,plain,(
    ! [A_9] : k5_xboole_0(A_9,'#skF_1') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_12])).

tff(c_442,plain,(
    ! [A_1] : k5_xboole_0('#skF_1',A_1) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_4,c_438])).

tff(c_192,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_169])).

tff(c_435,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_395])).

tff(c_557,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_197,c_442,c_435])).

tff(c_194,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_137])).

tff(c_558,plain,(
    k2_tarski('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_194])).

tff(c_28,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_571,plain,(
    k1_tarski('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_28])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:15:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.32  
% 2.49/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.33  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.49/1.33  
% 2.49/1.33  %Foreground sorts:
% 2.49/1.33  
% 2.49/1.33  
% 2.49/1.33  %Background operators:
% 2.49/1.33  
% 2.49/1.33  
% 2.49/1.33  %Foreground operators:
% 2.49/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.49/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.49/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.33  
% 2.49/1.34  tff(f_75, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.49/1.34  tff(f_79, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.49/1.34  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.49/1.34  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.49/1.34  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.49/1.34  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.49/1.34  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.49/1.34  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.49/1.34  tff(f_74, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.49/1.34  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.49/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.49/1.34  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.49/1.34  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.49/1.34  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.49/1.34  tff(c_48, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.49/1.34  tff(c_50, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.34  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.34  tff(c_123, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_14])).
% 2.49/1.34  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.49/1.34  tff(c_137, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_123, c_8])).
% 2.49/1.34  tff(c_154, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.49/1.34  tff(c_163, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_137, c_154])).
% 2.49/1.34  tff(c_169, plain, (k2_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_163])).
% 2.49/1.34  tff(c_183, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_169, c_14])).
% 2.49/1.34  tff(c_190, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_183, c_8])).
% 2.49/1.34  tff(c_18, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.49/1.34  tff(c_198, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_18])).
% 2.49/1.34  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.34  tff(c_282, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.34  tff(c_291, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_282])).
% 2.49/1.34  tff(c_294, plain, (![A_3]: (k4_xboole_0(A_3, A_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_291])).
% 2.49/1.34  tff(c_44, plain, (![B_67]: (k4_xboole_0(k1_tarski(B_67), k1_tarski(B_67))!=k1_tarski(B_67))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.34  tff(c_295, plain, (![B_67]: (k1_tarski(B_67)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_44])).
% 2.49/1.34  tff(c_10, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.34  tff(c_196, plain, (![A_8]: (k4_xboole_0('#skF_1', A_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_190, c_10])).
% 2.49/1.34  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.49/1.34  tff(c_395, plain, (![A_100, B_101]: (k5_xboole_0(k5_xboole_0(A_100, B_101), k2_xboole_0(A_100, B_101))=k3_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.34  tff(c_438, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_395])).
% 2.49/1.34  tff(c_443, plain, (![A_102]: (k5_xboole_0('#skF_1', A_102)=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_4, c_438])).
% 2.49/1.34  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.34  tff(c_456, plain, (![B_6]: (k4_xboole_0('#skF_1', B_6)=k3_xboole_0('#skF_1', B_6))), inference(superposition, [status(thm), theory('equality')], [c_443, c_6])).
% 2.49/1.34  tff(c_482, plain, (![B_6]: (k3_xboole_0('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_456])).
% 2.49/1.34  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.49/1.34  tff(c_197, plain, (![A_9]: (k5_xboole_0(A_9, '#skF_1')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_12])).
% 2.49/1.34  tff(c_442, plain, (![A_1]: (k5_xboole_0('#skF_1', A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_4, c_438])).
% 2.49/1.34  tff(c_192, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_169])).
% 2.49/1.34  tff(c_435, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_192, c_395])).
% 2.49/1.34  tff(c_557, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_482, c_197, c_442, c_435])).
% 2.49/1.34  tff(c_194, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_137])).
% 2.49/1.34  tff(c_558, plain, (k2_tarski('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_557, c_194])).
% 2.49/1.34  tff(c_28, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.49/1.34  tff(c_571, plain, (k1_tarski('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_558, c_28])).
% 2.49/1.34  tff(c_579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_571])).
% 2.49/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.34  
% 2.49/1.34  Inference rules
% 2.49/1.34  ----------------------
% 2.49/1.34  #Ref     : 0
% 2.49/1.34  #Sup     : 134
% 2.49/1.34  #Fact    : 0
% 2.49/1.34  #Define  : 0
% 2.49/1.34  #Split   : 0
% 2.49/1.34  #Chain   : 0
% 2.49/1.34  #Close   : 0
% 2.49/1.34  
% 2.49/1.34  Ordering : KBO
% 2.49/1.34  
% 2.49/1.34  Simplification rules
% 2.49/1.34  ----------------------
% 2.49/1.34  #Subsume      : 0
% 2.49/1.34  #Demod        : 64
% 2.49/1.34  #Tautology    : 103
% 2.49/1.34  #SimpNegUnit  : 3
% 2.49/1.34  #BackRed      : 15
% 2.49/1.34  
% 2.49/1.34  #Partial instantiations: 0
% 2.49/1.34  #Strategies tried      : 1
% 2.49/1.34  
% 2.49/1.34  Timing (in seconds)
% 2.49/1.34  ----------------------
% 2.49/1.34  Preprocessing        : 0.33
% 2.49/1.34  Parsing              : 0.17
% 2.49/1.34  CNF conversion       : 0.02
% 2.49/1.34  Main loop            : 0.23
% 2.49/1.34  Inferencing          : 0.08
% 2.49/1.34  Reduction            : 0.08
% 2.49/1.34  Demodulation         : 0.06
% 2.49/1.34  BG Simplification    : 0.02
% 2.49/1.34  Subsumption          : 0.03
% 2.49/1.34  Abstraction          : 0.02
% 2.49/1.34  MUC search           : 0.00
% 2.49/1.34  Cooper               : 0.00
% 2.49/1.34  Total                : 0.59
% 2.49/1.34  Index Insertion      : 0.00
% 2.49/1.34  Index Deletion       : 0.00
% 2.49/1.34  Index Matching       : 0.00
% 2.49/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
