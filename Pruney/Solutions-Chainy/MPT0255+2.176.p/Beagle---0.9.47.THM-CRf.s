%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:00 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(A_80,B_81) ),
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
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_291,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_282])).

tff(c_294,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_291])).

tff(c_44,plain,(
    ! [B_68] : k4_xboole_0(k1_tarski(B_68),k1_tarski(B_68)) != k1_tarski(B_68) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_295,plain,(
    ! [B_68] : k1_tarski(B_68) != '#skF_1' ),
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
    ! [A_101,B_102] : k5_xboole_0(k5_xboole_0(A_101,B_102),k2_xboole_0(A_101,B_102)) = k3_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_438,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_395])).

tff(c_443,plain,(
    ! [A_103] : k5_xboole_0('#skF_1',A_103) = A_103 ),
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
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_571,plain,(
    k1_tarski('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_28])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:34:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.29  
% 2.29/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.30  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.30  
% 2.29/1.30  %Foreground sorts:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Background operators:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Foreground operators:
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.29/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.29/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.29/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.29/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.29/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.29/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.30  
% 2.29/1.31  tff(f_75, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.29/1.31  tff(f_79, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.29/1.31  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.29/1.31  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.29/1.31  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.29/1.31  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.29/1.31  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.29/1.31  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.29/1.31  tff(f_74, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.29/1.31  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.29/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.29/1.31  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.29/1.31  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.29/1.31  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.29/1.31  tff(c_48, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.29/1.31  tff(c_50, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.29/1.31  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.29/1.31  tff(c_123, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_14])).
% 2.29/1.31  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.31  tff(c_137, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_123, c_8])).
% 2.29/1.31  tff(c_154, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.29/1.31  tff(c_163, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_137, c_154])).
% 2.29/1.31  tff(c_169, plain, (k2_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_163])).
% 2.29/1.31  tff(c_183, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_169, c_14])).
% 2.29/1.31  tff(c_190, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_183, c_8])).
% 2.29/1.31  tff(c_18, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.29/1.31  tff(c_198, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_18])).
% 2.29/1.31  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.31  tff(c_282, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.31  tff(c_291, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_282])).
% 2.29/1.31  tff(c_294, plain, (![A_3]: (k4_xboole_0(A_3, A_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_291])).
% 2.29/1.31  tff(c_44, plain, (![B_68]: (k4_xboole_0(k1_tarski(B_68), k1_tarski(B_68))!=k1_tarski(B_68))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.29/1.31  tff(c_295, plain, (![B_68]: (k1_tarski(B_68)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_44])).
% 2.29/1.31  tff(c_10, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.31  tff(c_196, plain, (![A_8]: (k4_xboole_0('#skF_1', A_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_190, c_10])).
% 2.29/1.31  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.29/1.31  tff(c_395, plain, (![A_101, B_102]: (k5_xboole_0(k5_xboole_0(A_101, B_102), k2_xboole_0(A_101, B_102))=k3_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.29/1.31  tff(c_438, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_395])).
% 2.29/1.31  tff(c_443, plain, (![A_103]: (k5_xboole_0('#skF_1', A_103)=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_4, c_438])).
% 2.29/1.31  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.31  tff(c_456, plain, (![B_6]: (k4_xboole_0('#skF_1', B_6)=k3_xboole_0('#skF_1', B_6))), inference(superposition, [status(thm), theory('equality')], [c_443, c_6])).
% 2.29/1.31  tff(c_482, plain, (![B_6]: (k3_xboole_0('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_456])).
% 2.29/1.31  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.29/1.31  tff(c_197, plain, (![A_9]: (k5_xboole_0(A_9, '#skF_1')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_12])).
% 2.29/1.31  tff(c_442, plain, (![A_1]: (k5_xboole_0('#skF_1', A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_4, c_438])).
% 2.29/1.31  tff(c_192, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_169])).
% 2.29/1.31  tff(c_435, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_192, c_395])).
% 2.29/1.31  tff(c_557, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_482, c_197, c_442, c_435])).
% 2.29/1.31  tff(c_194, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_137])).
% 2.29/1.31  tff(c_558, plain, (k2_tarski('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_557, c_194])).
% 2.29/1.31  tff(c_28, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.31  tff(c_571, plain, (k1_tarski('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_558, c_28])).
% 2.29/1.31  tff(c_579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_571])).
% 2.29/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  Inference rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Ref     : 0
% 2.29/1.31  #Sup     : 134
% 2.29/1.31  #Fact    : 0
% 2.29/1.31  #Define  : 0
% 2.29/1.31  #Split   : 0
% 2.29/1.31  #Chain   : 0
% 2.29/1.31  #Close   : 0
% 2.29/1.31  
% 2.29/1.31  Ordering : KBO
% 2.29/1.31  
% 2.29/1.31  Simplification rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Subsume      : 0
% 2.29/1.31  #Demod        : 64
% 2.29/1.31  #Tautology    : 103
% 2.29/1.31  #SimpNegUnit  : 3
% 2.29/1.31  #BackRed      : 15
% 2.29/1.31  
% 2.29/1.31  #Partial instantiations: 0
% 2.29/1.31  #Strategies tried      : 1
% 2.29/1.31  
% 2.29/1.31  Timing (in seconds)
% 2.29/1.31  ----------------------
% 2.29/1.31  Preprocessing        : 0.32
% 2.29/1.31  Parsing              : 0.17
% 2.29/1.31  CNF conversion       : 0.02
% 2.29/1.31  Main loop            : 0.22
% 2.29/1.31  Inferencing          : 0.08
% 2.29/1.31  Reduction            : 0.08
% 2.29/1.31  Demodulation         : 0.06
% 2.29/1.31  BG Simplification    : 0.02
% 2.29/1.31  Subsumption          : 0.03
% 2.29/1.31  Abstraction          : 0.02
% 2.29/1.31  MUC search           : 0.00
% 2.29/1.31  Cooper               : 0.00
% 2.29/1.31  Total                : 0.58
% 2.29/1.31  Index Insertion      : 0.00
% 2.29/1.31  Index Deletion       : 0.00
% 2.29/1.31  Index Matching       : 0.00
% 2.29/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
