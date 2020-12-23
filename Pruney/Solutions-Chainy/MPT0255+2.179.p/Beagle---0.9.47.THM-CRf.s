%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

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
% Statistics : Number of formulae       :   72 ( 215 expanded)
%              Number of leaves         :   33 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          :   55 ( 232 expanded)
%              Number of equality atoms :   54 ( 231 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_73,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_75,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(c_46,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_50,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | k2_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_122,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_6])).

tff(c_148,plain,(
    ! [A_86,B_87] : k3_tarski(k2_tarski(A_86,B_87)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_157,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_148])).

tff(c_163,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_157])).

tff(c_213,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_6])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_177,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_186,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_177])).

tff(c_189,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_186])).

tff(c_42,plain,(
    ! [B_73] : k4_xboole_0(k1_tarski(B_73),k1_tarski(B_73)) != k1_tarski(B_73) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_190,plain,(
    ! [B_73] : k1_tarski(B_73) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_42])).

tff(c_216,plain,(
    ! [B_73] : k1_tarski(B_73) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_190])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_221,plain,(
    ! [A_7] : k4_xboole_0('#skF_1',A_7) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_213,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_223,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_14])).

tff(c_48,plain,(
    ! [A_74] : k3_tarski(k1_tarski(A_74)) = A_74 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_160,plain,(
    ! [A_42] : k3_tarski(k1_tarski(A_42)) = k2_xboole_0(A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_148])).

tff(c_164,plain,(
    ! [A_42] : k2_xboole_0(A_42,A_42) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_160])).

tff(c_344,plain,(
    ! [A_105,B_106] : k5_xboole_0(k5_xboole_0(A_105,B_106),k2_xboole_0(A_105,B_106)) = k3_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_374,plain,(
    ! [A_42] : k5_xboole_0(k5_xboole_0(A_42,A_42),A_42) = k3_xboole_0(A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_344])).

tff(c_379,plain,(
    ! [A_107] : k5_xboole_0('#skF_1',A_107) = A_107 ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_2,c_374])).

tff(c_412,plain,(
    ! [B_4] : k4_xboole_0('#skF_1',B_4) = k3_xboole_0('#skF_1',B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_379])).

tff(c_420,plain,(
    ! [B_4] : k3_xboole_0('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_412])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_222,plain,(
    ! [A_8] : k5_xboole_0(A_8,'#skF_1') = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_10])).

tff(c_378,plain,(
    ! [A_42] : k5_xboole_0('#skF_1',A_42) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_2,c_374])).

tff(c_215,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_163])).

tff(c_362,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_344])).

tff(c_525,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_222,c_378,c_362])).

tff(c_219,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_122])).

tff(c_527,plain,(
    k2_tarski('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_219])).

tff(c_539,plain,(
    k1_tarski('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_26])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.30  
% 2.29/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.30  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
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
% 2.29/1.31  tff(f_73, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.29/1.31  tff(f_79, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.29/1.31  tff(f_33, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.29/1.31  tff(f_67, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.29/1.31  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.29/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.29/1.31  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.29/1.31  tff(f_72, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.29/1.31  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.29/1.31  tff(f_75, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.29/1.31  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.29/1.31  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.29/1.31  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.29/1.31  tff(c_46, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.29/1.31  tff(c_50, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.29/1.31  tff(c_6, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | k2_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.29/1.31  tff(c_122, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_50, c_6])).
% 2.29/1.31  tff(c_148, plain, (![A_86, B_87]: (k3_tarski(k2_tarski(A_86, B_87))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.31  tff(c_157, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_122, c_148])).
% 2.29/1.31  tff(c_163, plain, (k2_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_157])).
% 2.29/1.31  tff(c_213, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_163, c_6])).
% 2.29/1.31  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.29/1.31  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.29/1.31  tff(c_177, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.31  tff(c_186, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_177])).
% 2.29/1.31  tff(c_189, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_186])).
% 2.29/1.31  tff(c_42, plain, (![B_73]: (k4_xboole_0(k1_tarski(B_73), k1_tarski(B_73))!=k1_tarski(B_73))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.29/1.31  tff(c_190, plain, (![B_73]: (k1_tarski(B_73)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_189, c_42])).
% 2.29/1.31  tff(c_216, plain, (![B_73]: (k1_tarski(B_73)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_190])).
% 2.29/1.31  tff(c_8, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.31  tff(c_221, plain, (![A_7]: (k4_xboole_0('#skF_1', A_7)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_213, c_8])).
% 2.29/1.31  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.31  tff(c_223, plain, (![A_12]: (k5_xboole_0(A_12, A_12)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_14])).
% 2.29/1.31  tff(c_48, plain, (![A_74]: (k3_tarski(k1_tarski(A_74))=A_74)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.29/1.31  tff(c_26, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.29/1.31  tff(c_160, plain, (![A_42]: (k3_tarski(k1_tarski(A_42))=k2_xboole_0(A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_26, c_148])).
% 2.29/1.31  tff(c_164, plain, (![A_42]: (k2_xboole_0(A_42, A_42)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_160])).
% 2.29/1.31  tff(c_344, plain, (![A_105, B_106]: (k5_xboole_0(k5_xboole_0(A_105, B_106), k2_xboole_0(A_105, B_106))=k3_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.31  tff(c_374, plain, (![A_42]: (k5_xboole_0(k5_xboole_0(A_42, A_42), A_42)=k3_xboole_0(A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_164, c_344])).
% 2.29/1.31  tff(c_379, plain, (![A_107]: (k5_xboole_0('#skF_1', A_107)=A_107)), inference(demodulation, [status(thm), theory('equality')], [c_223, c_2, c_374])).
% 2.29/1.31  tff(c_412, plain, (![B_4]: (k4_xboole_0('#skF_1', B_4)=k3_xboole_0('#skF_1', B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_379])).
% 2.29/1.31  tff(c_420, plain, (![B_4]: (k3_xboole_0('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_412])).
% 2.29/1.31  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.31  tff(c_222, plain, (![A_8]: (k5_xboole_0(A_8, '#skF_1')=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_10])).
% 2.29/1.31  tff(c_378, plain, (![A_42]: (k5_xboole_0('#skF_1', A_42)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_223, c_2, c_374])).
% 2.29/1.31  tff(c_215, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_213, c_163])).
% 2.29/1.31  tff(c_362, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_215, c_344])).
% 2.29/1.31  tff(c_525, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_420, c_222, c_378, c_362])).
% 2.29/1.31  tff(c_219, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_213, c_122])).
% 2.29/1.31  tff(c_527, plain, (k2_tarski('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_525, c_219])).
% 2.29/1.31  tff(c_539, plain, (k1_tarski('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_527, c_26])).
% 2.29/1.31  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_216, c_539])).
% 2.29/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  Inference rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Ref     : 0
% 2.29/1.31  #Sup     : 126
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
% 2.29/1.31  #Demod        : 50
% 2.29/1.31  #Tautology    : 106
% 2.29/1.31  #SimpNegUnit  : 3
% 2.29/1.31  #BackRed      : 15
% 2.29/1.31  
% 2.29/1.31  #Partial instantiations: 0
% 2.29/1.31  #Strategies tried      : 1
% 2.29/1.31  
% 2.29/1.31  Timing (in seconds)
% 2.29/1.31  ----------------------
% 2.29/1.31  Preprocessing        : 0.33
% 2.29/1.31  Parsing              : 0.17
% 2.29/1.31  CNF conversion       : 0.02
% 2.29/1.31  Main loop            : 0.21
% 2.29/1.31  Inferencing          : 0.07
% 2.29/1.31  Reduction            : 0.08
% 2.29/1.31  Demodulation         : 0.06
% 2.29/1.31  BG Simplification    : 0.02
% 2.29/1.31  Subsumption          : 0.02
% 2.29/1.31  Abstraction          : 0.02
% 2.29/1.31  MUC search           : 0.00
% 2.29/1.31  Cooper               : 0.00
% 2.29/1.31  Total                : 0.56
% 2.29/1.31  Index Insertion      : 0.00
% 2.29/1.32  Index Deletion       : 0.00
% 2.29/1.32  Index Matching       : 0.00
% 2.29/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
