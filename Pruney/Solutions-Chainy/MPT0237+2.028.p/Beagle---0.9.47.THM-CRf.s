%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:48 EST 2020

% Result     : Theorem 12.70s
% Output     : CNFRefutation 12.70s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 128 expanded)
%              Number of leaves         :   36 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 135 expanded)
%              Number of equality atoms :   56 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_188,plain,(
    ! [A_81] : k3_xboole_0(k1_xboole_0,A_81) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_159])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_196,plain,(
    ! [A_81] : k3_xboole_0(A_81,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_520,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_535,plain,(
    ! [A_81] : k5_xboole_0(A_81,k1_xboole_0) = k4_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_520])).

tff(c_549,plain,(
    ! [A_81] : k5_xboole_0(A_81,k1_xboole_0) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_535])).

tff(c_26,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_81,plain,(
    ! [B_64,C_65] : r1_tarski(k1_tarski(B_64),k2_tarski(B_64,C_65)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_84,plain,(
    ! [A_20] : r1_tarski(k1_tarski(A_20),k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_81])).

tff(c_259,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = k1_xboole_0
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_283,plain,(
    ! [A_20] : k4_xboole_0(k1_tarski(A_20),k1_tarski(A_20)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_259])).

tff(c_544,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_520])).

tff(c_780,plain,(
    ! [A_123,B_124] : k5_xboole_0(k5_xboole_0(A_123,B_124),k3_xboole_0(A_123,B_124)) = k2_xboole_0(A_123,B_124) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17] : k5_xboole_0(k5_xboole_0(A_15,B_16),C_17) = k5_xboole_0(A_15,k5_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_792,plain,(
    ! [A_123,B_124] : k5_xboole_0(A_123,k5_xboole_0(B_124,k3_xboole_0(A_123,B_124))) = k2_xboole_0(A_123,B_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_22])).

tff(c_1013,plain,(
    ! [A_132,B_133] : k5_xboole_0(A_132,k4_xboole_0(B_133,A_132)) = k2_xboole_0(A_132,B_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_792])).

tff(c_1048,plain,(
    ! [A_20] : k2_xboole_0(k1_tarski(A_20),k1_tarski(A_20)) = k5_xboole_0(k1_tarski(A_20),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_1013])).

tff(c_1221,plain,(
    ! [A_148] : k2_xboole_0(k1_tarski(A_148),k1_tarski(A_148)) = k1_tarski(A_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_1048])).

tff(c_407,plain,(
    ! [A_97,B_98] : k3_tarski(k2_tarski(A_97,B_98)) = k2_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_416,plain,(
    ! [A_20] : k3_tarski(k1_tarski(A_20)) = k2_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_407])).

tff(c_1227,plain,(
    ! [A_148] : k3_tarski(k1_tarski(k1_tarski(A_148))) = k1_tarski(A_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_1221,c_416])).

tff(c_402,plain,(
    ! [A_95,B_96] :
      ( r1_xboole_0(k1_tarski(A_95),k1_tarski(B_96))
      | B_96 = A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1688,plain,(
    ! [A_175,B_176] :
      ( k4_xboole_0(k1_tarski(A_175),k1_tarski(B_176)) = k1_tarski(A_175)
      | B_176 = A_175 ) ),
    inference(resolution,[status(thm)],[c_402,c_18])).

tff(c_841,plain,(
    ! [A_123,B_124] : k5_xboole_0(A_123,k4_xboole_0(B_124,A_123)) = k2_xboole_0(A_123,B_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_792])).

tff(c_11819,plain,(
    ! [B_318,A_319] :
      ( k5_xboole_0(k1_tarski(B_318),k1_tarski(A_319)) = k2_xboole_0(k1_tarski(B_318),k1_tarski(A_319))
      | B_318 = A_319 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1688,c_841])).

tff(c_56,plain,(
    ! [A_57,B_58] :
      ( k5_xboole_0(k1_tarski(A_57),k1_tarski(B_58)) = k2_tarski(A_57,B_58)
      | B_58 = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28591,plain,(
    ! [B_473,A_474] :
      ( k2_xboole_0(k1_tarski(B_473),k1_tarski(A_474)) = k2_tarski(B_473,A_474)
      | B_473 = A_474
      | B_473 = A_474 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11819,c_56])).

tff(c_50,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_58,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_59,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_58])).

tff(c_28653,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_28591,c_59])).

tff(c_28659,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28653,c_28653,c_59])).

tff(c_28662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1227,c_416,c_26,c_28659])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:54:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.70/5.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.70/5.77  
% 12.70/5.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.70/5.77  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 12.70/5.77  
% 12.70/5.77  %Foreground sorts:
% 12.70/5.77  
% 12.70/5.77  
% 12.70/5.77  %Background operators:
% 12.70/5.77  
% 12.70/5.77  
% 12.70/5.77  %Foreground operators:
% 12.70/5.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.70/5.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.70/5.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.70/5.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.70/5.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.70/5.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.70/5.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.70/5.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.70/5.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.70/5.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.70/5.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.70/5.77  tff('#skF_2', type, '#skF_2': $i).
% 12.70/5.77  tff('#skF_1', type, '#skF_1': $i).
% 12.70/5.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.70/5.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.70/5.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.70/5.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.70/5.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.70/5.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.70/5.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.70/5.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.70/5.77  
% 12.70/5.78  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 12.70/5.78  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.70/5.78  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.70/5.78  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.70/5.78  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.70/5.78  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 12.70/5.78  tff(f_80, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 12.70/5.78  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.70/5.78  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 12.70/5.78  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.70/5.78  tff(f_82, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 12.70/5.78  tff(f_87, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 12.70/5.78  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 12.70/5.78  tff(f_94, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 12.70/5.78  tff(f_97, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 12.70/5.78  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.70/5.78  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.70/5.78  tff(c_159, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.70/5.78  tff(c_188, plain, (![A_81]: (k3_xboole_0(k1_xboole_0, A_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_159])).
% 12.70/5.78  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.70/5.78  tff(c_196, plain, (![A_81]: (k3_xboole_0(A_81, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_188, c_2])).
% 12.70/5.78  tff(c_520, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.70/5.78  tff(c_535, plain, (![A_81]: (k5_xboole_0(A_81, k1_xboole_0)=k4_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_196, c_520])).
% 12.70/5.78  tff(c_549, plain, (![A_81]: (k5_xboole_0(A_81, k1_xboole_0)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_535])).
% 12.70/5.78  tff(c_26, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.70/5.78  tff(c_81, plain, (![B_64, C_65]: (r1_tarski(k1_tarski(B_64), k2_tarski(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.70/5.78  tff(c_84, plain, (![A_20]: (r1_tarski(k1_tarski(A_20), k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_81])).
% 12.70/5.78  tff(c_259, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=k1_xboole_0 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.70/5.78  tff(c_283, plain, (![A_20]: (k4_xboole_0(k1_tarski(A_20), k1_tarski(A_20))=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_259])).
% 12.70/5.78  tff(c_544, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_520])).
% 12.70/5.78  tff(c_780, plain, (![A_123, B_124]: (k5_xboole_0(k5_xboole_0(A_123, B_124), k3_xboole_0(A_123, B_124))=k2_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.70/5.78  tff(c_22, plain, (![A_15, B_16, C_17]: (k5_xboole_0(k5_xboole_0(A_15, B_16), C_17)=k5_xboole_0(A_15, k5_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.70/5.78  tff(c_792, plain, (![A_123, B_124]: (k5_xboole_0(A_123, k5_xboole_0(B_124, k3_xboole_0(A_123, B_124)))=k2_xboole_0(A_123, B_124))), inference(superposition, [status(thm), theory('equality')], [c_780, c_22])).
% 12.70/5.78  tff(c_1013, plain, (![A_132, B_133]: (k5_xboole_0(A_132, k4_xboole_0(B_133, A_132))=k2_xboole_0(A_132, B_133))), inference(demodulation, [status(thm), theory('equality')], [c_544, c_792])).
% 12.70/5.78  tff(c_1048, plain, (![A_20]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(A_20))=k5_xboole_0(k1_tarski(A_20), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_283, c_1013])).
% 12.70/5.78  tff(c_1221, plain, (![A_148]: (k2_xboole_0(k1_tarski(A_148), k1_tarski(A_148))=k1_tarski(A_148))), inference(demodulation, [status(thm), theory('equality')], [c_549, c_1048])).
% 12.70/5.78  tff(c_407, plain, (![A_97, B_98]: (k3_tarski(k2_tarski(A_97, B_98))=k2_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.70/5.78  tff(c_416, plain, (![A_20]: (k3_tarski(k1_tarski(A_20))=k2_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_26, c_407])).
% 12.70/5.78  tff(c_1227, plain, (![A_148]: (k3_tarski(k1_tarski(k1_tarski(A_148)))=k1_tarski(A_148))), inference(superposition, [status(thm), theory('equality')], [c_1221, c_416])).
% 12.70/5.78  tff(c_402, plain, (![A_95, B_96]: (r1_xboole_0(k1_tarski(A_95), k1_tarski(B_96)) | B_96=A_95)), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.70/5.78  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.70/5.78  tff(c_1688, plain, (![A_175, B_176]: (k4_xboole_0(k1_tarski(A_175), k1_tarski(B_176))=k1_tarski(A_175) | B_176=A_175)), inference(resolution, [status(thm)], [c_402, c_18])).
% 12.70/5.78  tff(c_841, plain, (![A_123, B_124]: (k5_xboole_0(A_123, k4_xboole_0(B_124, A_123))=k2_xboole_0(A_123, B_124))), inference(demodulation, [status(thm), theory('equality')], [c_544, c_792])).
% 12.70/5.78  tff(c_11819, plain, (![B_318, A_319]: (k5_xboole_0(k1_tarski(B_318), k1_tarski(A_319))=k2_xboole_0(k1_tarski(B_318), k1_tarski(A_319)) | B_318=A_319)), inference(superposition, [status(thm), theory('equality')], [c_1688, c_841])).
% 12.70/5.78  tff(c_56, plain, (![A_57, B_58]: (k5_xboole_0(k1_tarski(A_57), k1_tarski(B_58))=k2_tarski(A_57, B_58) | B_58=A_57)), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.70/5.78  tff(c_28591, plain, (![B_473, A_474]: (k2_xboole_0(k1_tarski(B_473), k1_tarski(A_474))=k2_tarski(B_473, A_474) | B_473=A_474 | B_473=A_474)), inference(superposition, [status(thm), theory('equality')], [c_11819, c_56])).
% 12.70/5.78  tff(c_50, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.70/5.78  tff(c_58, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.70/5.78  tff(c_59, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_58])).
% 12.70/5.78  tff(c_28653, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_28591, c_59])).
% 12.70/5.78  tff(c_28659, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28653, c_28653, c_59])).
% 12.70/5.78  tff(c_28662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1227, c_416, c_26, c_28659])).
% 12.70/5.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.70/5.78  
% 12.70/5.78  Inference rules
% 12.70/5.78  ----------------------
% 12.70/5.78  #Ref     : 0
% 12.70/5.78  #Sup     : 7022
% 12.70/5.78  #Fact    : 7
% 12.70/5.78  #Define  : 0
% 12.70/5.78  #Split   : 1
% 12.70/5.78  #Chain   : 0
% 12.70/5.78  #Close   : 0
% 12.70/5.78  
% 12.70/5.78  Ordering : KBO
% 12.70/5.78  
% 12.70/5.78  Simplification rules
% 12.70/5.78  ----------------------
% 12.70/5.78  #Subsume      : 1242
% 12.70/5.78  #Demod        : 10270
% 12.70/5.78  #Tautology    : 3347
% 12.70/5.78  #SimpNegUnit  : 116
% 12.70/5.78  #BackRed      : 2
% 12.70/5.78  
% 12.70/5.78  #Partial instantiations: 0
% 12.70/5.78  #Strategies tried      : 1
% 12.70/5.78  
% 12.70/5.78  Timing (in seconds)
% 12.70/5.78  ----------------------
% 12.91/5.78  Preprocessing        : 0.34
% 12.91/5.78  Parsing              : 0.19
% 12.91/5.78  CNF conversion       : 0.02
% 12.91/5.78  Main loop            : 4.63
% 12.91/5.78  Inferencing          : 0.90
% 12.91/5.78  Reduction            : 2.75
% 12.91/5.78  Demodulation         : 2.48
% 12.91/5.78  BG Simplification    : 0.12
% 12.91/5.78  Subsumption          : 0.66
% 12.91/5.78  Abstraction          : 0.24
% 12.91/5.78  MUC search           : 0.00
% 12.91/5.78  Cooper               : 0.00
% 12.91/5.79  Total                : 5.01
% 12.91/5.79  Index Insertion      : 0.00
% 12.91/5.79  Index Deletion       : 0.00
% 12.91/5.79  Index Matching       : 0.00
% 12.91/5.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
