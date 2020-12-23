%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:00 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 203 expanded)
%              Number of leaves         :   33 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :   52 ( 220 expanded)
%              Number of equality atoms :   51 ( 219 expanded)
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

tff(f_75,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
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

tff(f_45,axiom,(
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

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k1_xboole_0 = A_7
      | k2_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_141,plain,(
    ! [A_84,B_85] : k3_tarski(k2_tarski(A_84,B_85)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_150,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_141])).

tff(c_156,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_150])).

tff(c_173,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_8])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_181,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_16])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_264,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_273,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_264])).

tff(c_276,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_273])).

tff(c_44,plain,(
    ! [B_75] : k4_xboole_0(k1_tarski(B_75),k1_tarski(B_75)) != k1_tarski(B_75) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_277,plain,(
    ! [B_75] : k1_tarski(B_75) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_44])).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_179,plain,(
    ! [A_9] : k4_xboole_0('#skF_1',A_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_10])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_441,plain,(
    ! [A_113,B_114] : k5_xboole_0(k5_xboole_0(A_113,B_114),k2_xboole_0(A_113,B_114)) = k3_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_471,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_441])).

tff(c_476,plain,(
    ! [A_115] : k5_xboole_0('#skF_1',A_115) = A_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_4,c_471])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_486,plain,(
    ! [B_6] : k4_xboole_0('#skF_1',B_6) = k3_xboole_0('#skF_1',B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_6])).

tff(c_511,plain,(
    ! [B_6] : k3_xboole_0('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_486])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_180,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_1') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_12])).

tff(c_475,plain,(
    ! [A_1] : k5_xboole_0('#skF_1',A_1) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_4,c_471])).

tff(c_175,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_156])).

tff(c_459,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_441])).

tff(c_548,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_180,c_475,c_459])).

tff(c_177,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_125])).

tff(c_549,plain,(
    k2_tarski('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_177])).

tff(c_28,plain,(
    ! [A_44] : k2_tarski(A_44,A_44) = k1_tarski(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_562,plain,(
    k1_tarski('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_28])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.31  
% 2.18/1.31  %Foreground sorts:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Background operators:
% 2.18/1.31  
% 2.18/1.31  
% 2.18/1.31  %Foreground operators:
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.18/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.18/1.31  
% 2.46/1.32  tff(f_75, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.46/1.32  tff(f_79, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.46/1.32  tff(f_35, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.46/1.32  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.46/1.32  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.46/1.32  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.46/1.32  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.46/1.32  tff(f_74, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.46/1.32  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.46/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.46/1.32  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.46/1.32  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.46/1.32  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.46/1.32  tff(c_48, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.32  tff(c_50, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.46/1.33  tff(c_8, plain, (![A_7, B_8]: (k1_xboole_0=A_7 | k2_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.46/1.33  tff(c_125, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_50, c_8])).
% 2.46/1.33  tff(c_141, plain, (![A_84, B_85]: (k3_tarski(k2_tarski(A_84, B_85))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.46/1.33  tff(c_150, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_141])).
% 2.46/1.33  tff(c_156, plain, (k2_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_150])).
% 2.46/1.33  tff(c_173, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_156, c_8])).
% 2.46/1.33  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.33  tff(c_181, plain, (![A_14]: (k5_xboole_0(A_14, A_14)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_16])).
% 2.46/1.33  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.33  tff(c_264, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.33  tff(c_273, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_264])).
% 2.46/1.33  tff(c_276, plain, (![A_3]: (k4_xboole_0(A_3, A_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_273])).
% 2.46/1.33  tff(c_44, plain, (![B_75]: (k4_xboole_0(k1_tarski(B_75), k1_tarski(B_75))!=k1_tarski(B_75))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.46/1.33  tff(c_277, plain, (![B_75]: (k1_tarski(B_75)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_44])).
% 2.46/1.33  tff(c_10, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.33  tff(c_179, plain, (![A_9]: (k4_xboole_0('#skF_1', A_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_10])).
% 2.46/1.33  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.33  tff(c_441, plain, (![A_113, B_114]: (k5_xboole_0(k5_xboole_0(A_113, B_114), k2_xboole_0(A_113, B_114))=k3_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.46/1.33  tff(c_471, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_441])).
% 2.46/1.33  tff(c_476, plain, (![A_115]: (k5_xboole_0('#skF_1', A_115)=A_115)), inference(demodulation, [status(thm), theory('equality')], [c_181, c_4, c_471])).
% 2.46/1.33  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.33  tff(c_486, plain, (![B_6]: (k4_xboole_0('#skF_1', B_6)=k3_xboole_0('#skF_1', B_6))), inference(superposition, [status(thm), theory('equality')], [c_476, c_6])).
% 2.46/1.33  tff(c_511, plain, (![B_6]: (k3_xboole_0('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_486])).
% 2.46/1.33  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.46/1.33  tff(c_180, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_1')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_173, c_12])).
% 2.46/1.33  tff(c_475, plain, (![A_1]: (k5_xboole_0('#skF_1', A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_181, c_4, c_471])).
% 2.46/1.33  tff(c_175, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_156])).
% 2.46/1.33  tff(c_459, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_175, c_441])).
% 2.46/1.33  tff(c_548, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_511, c_180, c_475, c_459])).
% 2.46/1.33  tff(c_177, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_125])).
% 2.46/1.33  tff(c_549, plain, (k2_tarski('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_548, c_177])).
% 2.46/1.33  tff(c_28, plain, (![A_44]: (k2_tarski(A_44, A_44)=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.46/1.33  tff(c_562, plain, (k1_tarski('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_549, c_28])).
% 2.46/1.33  tff(c_570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_277, c_562])).
% 2.46/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.33  
% 2.46/1.33  Inference rules
% 2.46/1.33  ----------------------
% 2.46/1.33  #Ref     : 0
% 2.46/1.33  #Sup     : 132
% 2.46/1.33  #Fact    : 0
% 2.46/1.33  #Define  : 0
% 2.46/1.33  #Split   : 0
% 2.46/1.33  #Chain   : 0
% 2.46/1.33  #Close   : 0
% 2.46/1.33  
% 2.46/1.33  Ordering : KBO
% 2.46/1.33  
% 2.46/1.33  Simplification rules
% 2.46/1.33  ----------------------
% 2.46/1.33  #Subsume      : 1
% 2.46/1.33  #Demod        : 47
% 2.46/1.33  #Tautology    : 112
% 2.46/1.33  #SimpNegUnit  : 3
% 2.46/1.33  #BackRed      : 13
% 2.46/1.33  
% 2.46/1.33  #Partial instantiations: 0
% 2.46/1.33  #Strategies tried      : 1
% 2.46/1.33  
% 2.46/1.33  Timing (in seconds)
% 2.46/1.33  ----------------------
% 2.46/1.33  Preprocessing        : 0.33
% 2.46/1.33  Parsing              : 0.17
% 2.46/1.33  CNF conversion       : 0.02
% 2.46/1.33  Main loop            : 0.22
% 2.46/1.33  Inferencing          : 0.08
% 2.46/1.33  Reduction            : 0.08
% 2.46/1.33  Demodulation         : 0.06
% 2.46/1.33  BG Simplification    : 0.02
% 2.46/1.33  Subsumption          : 0.03
% 2.46/1.33  Abstraction          : 0.02
% 2.46/1.33  MUC search           : 0.00
% 2.46/1.33  Cooper               : 0.00
% 2.46/1.33  Total                : 0.58
% 2.46/1.33  Index Insertion      : 0.00
% 2.46/1.33  Index Deletion       : 0.00
% 2.46/1.33  Index Matching       : 0.00
% 2.46/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
