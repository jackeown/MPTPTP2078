%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:26 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 326 expanded)
%              Number of leaves         :   37 ( 129 expanded)
%              Depth                    :   17
%              Number of atoms          :   87 ( 430 expanded)
%              Number of equality atoms :   64 ( 372 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_569,plain,(
    ! [A_108,B_109] : k5_xboole_0(k5_xboole_0(A_108,B_109),k2_xboole_0(A_108,B_109)) = k3_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_633,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_569])).

tff(c_642,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20,c_633])).

tff(c_430,plain,(
    ! [A_101,B_102,C_103] : k5_xboole_0(k5_xboole_0(A_101,B_102),C_103) = k5_xboole_0(A_101,k5_xboole_0(B_102,C_103)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_480,plain,(
    ! [A_18,C_103] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_103)) = k5_xboole_0(k1_xboole_0,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_430])).

tff(c_883,plain,(
    ! [A_122,C_123] : k5_xboole_0(A_122,k5_xboole_0(A_122,C_123)) = C_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_480])).

tff(c_938,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_883])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_58,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_90,plain,(
    ! [A_62,B_63] : r1_tarski(A_62,k2_xboole_0(A_62,B_63)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_90])).

tff(c_367,plain,(
    ! [B_99,A_100] :
      ( k1_tarski(B_99) = A_100
      | k1_xboole_0 = A_100
      | ~ r1_tarski(A_100,k1_tarski(B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_374,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_93,c_367])).

tff(c_385,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_374])).

tff(c_392,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_58])).

tff(c_599,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_569])).

tff(c_640,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_599])).

tff(c_958,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_640])).

tff(c_56,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_912,plain,(
    k5_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_883])).

tff(c_952,plain,(
    k5_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_912])).

tff(c_42,plain,(
    ! [A_51,B_52] :
      ( r1_xboole_0(k1_tarski(A_51),B_52)
      | r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_419,plain,(
    ! [B_52] :
      ( r1_xboole_0('#skF_2',B_52)
      | r2_hidden('#skF_1',B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_42])).

tff(c_222,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k1_tarski(A_82),B_83)
      | ~ r2_hidden(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_226,plain,(
    ! [A_82,B_83] :
      ( k2_xboole_0(k1_tarski(A_82),B_83) = B_83
      | ~ r2_hidden(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_222,c_10])).

tff(c_757,plain,(
    ! [B_112] :
      ( k2_xboole_0('#skF_2',B_112) = B_112
      | ~ r2_hidden('#skF_1',B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_226])).

tff(c_846,plain,(
    ! [B_120] :
      ( k2_xboole_0('#skF_2',B_120) = B_120
      | r1_xboole_0('#skF_2',B_120) ) ),
    inference(resolution,[status(thm)],[c_419,c_757])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1429,plain,(
    ! [B_142] :
      ( k4_xboole_0('#skF_2',B_142) = '#skF_2'
      | k2_xboole_0('#skF_2',B_142) = B_142 ) ),
    inference(resolution,[status(thm)],[c_846,c_14])).

tff(c_882,plain,(
    ! [A_18,C_103] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_103)) = C_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_480])).

tff(c_1346,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_882])).

tff(c_1435,plain,
    ( k5_xboole_0('#skF_3','#skF_2') = '#skF_2'
    | k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1429,c_1346])).

tff(c_1457,plain,
    ( k4_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_952,c_1435])).

tff(c_1458,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1457])).

tff(c_1047,plain,(
    k5_xboole_0('#skF_2','#skF_3') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_8])).

tff(c_959,plain,(
    ! [A_124,B_125] : k5_xboole_0(A_124,k5_xboole_0(B_125,A_124)) = B_125 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_883])).

tff(c_995,plain,(
    ! [A_18,C_103] : k5_xboole_0(k5_xboole_0(A_18,C_103),C_103) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_959])).

tff(c_1301,plain,(
    k5_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1047,c_995])).

tff(c_1469,plain,(
    k5_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1301])).

tff(c_22,plain,(
    ! [A_19,B_20] : k5_xboole_0(k5_xboole_0(A_19,B_20),k2_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1527,plain,(
    k5_xboole_0('#skF_2',k2_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1469,c_22])).

tff(c_1547,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_20,c_392,c_1527])).

tff(c_1549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1547])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:28:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.55  
% 3.25/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.56  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.25/1.56  
% 3.25/1.56  %Foreground sorts:
% 3.25/1.56  
% 3.25/1.56  
% 3.25/1.56  %Background operators:
% 3.25/1.56  
% 3.25/1.56  
% 3.25/1.56  %Foreground operators:
% 3.25/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.25/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.25/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.25/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.25/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.56  
% 3.40/1.57  tff(f_93, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.40/1.57  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.40/1.57  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.40/1.57  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.40/1.57  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.40/1.57  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.40/1.57  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.40/1.57  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.40/1.57  tff(f_78, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.40/1.57  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.40/1.57  tff(f_72, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.40/1.57  tff(f_67, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.40/1.57  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.40/1.57  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.40/1.57  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.40/1.57  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.57  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.57  tff(c_20, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.40/1.57  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.40/1.57  tff(c_569, plain, (![A_108, B_109]: (k5_xboole_0(k5_xboole_0(A_108, B_109), k2_xboole_0(A_108, B_109))=k3_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.57  tff(c_633, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_569])).
% 3.40/1.57  tff(c_642, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20, c_633])).
% 3.40/1.57  tff(c_430, plain, (![A_101, B_102, C_103]: (k5_xboole_0(k5_xboole_0(A_101, B_102), C_103)=k5_xboole_0(A_101, k5_xboole_0(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.57  tff(c_480, plain, (![A_18, C_103]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_103))=k5_xboole_0(k1_xboole_0, C_103))), inference(superposition, [status(thm), theory('equality')], [c_20, c_430])).
% 3.40/1.57  tff(c_883, plain, (![A_122, C_123]: (k5_xboole_0(A_122, k5_xboole_0(A_122, C_123))=C_123)), inference(demodulation, [status(thm), theory('equality')], [c_642, c_480])).
% 3.40/1.57  tff(c_938, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_883])).
% 3.40/1.57  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.40/1.57  tff(c_58, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.40/1.57  tff(c_90, plain, (![A_62, B_63]: (r1_tarski(A_62, k2_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.40/1.57  tff(c_93, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_90])).
% 3.40/1.57  tff(c_367, plain, (![B_99, A_100]: (k1_tarski(B_99)=A_100 | k1_xboole_0=A_100 | ~r1_tarski(A_100, k1_tarski(B_99)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.40/1.57  tff(c_374, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_93, c_367])).
% 3.40/1.57  tff(c_385, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_374])).
% 3.40/1.57  tff(c_392, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_385, c_58])).
% 3.40/1.57  tff(c_599, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_392, c_569])).
% 3.40/1.57  tff(c_640, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_599])).
% 3.40/1.57  tff(c_958, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_938, c_640])).
% 3.40/1.57  tff(c_56, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.40/1.57  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.40/1.57  tff(c_912, plain, (k5_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_640, c_883])).
% 3.40/1.57  tff(c_952, plain, (k5_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_912])).
% 3.40/1.57  tff(c_42, plain, (![A_51, B_52]: (r1_xboole_0(k1_tarski(A_51), B_52) | r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.57  tff(c_419, plain, (![B_52]: (r1_xboole_0('#skF_2', B_52) | r2_hidden('#skF_1', B_52))), inference(superposition, [status(thm), theory('equality')], [c_385, c_42])).
% 3.40/1.57  tff(c_222, plain, (![A_82, B_83]: (r1_tarski(k1_tarski(A_82), B_83) | ~r2_hidden(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.40/1.57  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.40/1.57  tff(c_226, plain, (![A_82, B_83]: (k2_xboole_0(k1_tarski(A_82), B_83)=B_83 | ~r2_hidden(A_82, B_83))), inference(resolution, [status(thm)], [c_222, c_10])).
% 3.40/1.57  tff(c_757, plain, (![B_112]: (k2_xboole_0('#skF_2', B_112)=B_112 | ~r2_hidden('#skF_1', B_112))), inference(superposition, [status(thm), theory('equality')], [c_385, c_226])).
% 3.40/1.57  tff(c_846, plain, (![B_120]: (k2_xboole_0('#skF_2', B_120)=B_120 | r1_xboole_0('#skF_2', B_120))), inference(resolution, [status(thm)], [c_419, c_757])).
% 3.40/1.57  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.40/1.57  tff(c_1429, plain, (![B_142]: (k4_xboole_0('#skF_2', B_142)='#skF_2' | k2_xboole_0('#skF_2', B_142)=B_142)), inference(resolution, [status(thm)], [c_846, c_14])).
% 3.40/1.57  tff(c_882, plain, (![A_18, C_103]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_103))=C_103)), inference(demodulation, [status(thm), theory('equality')], [c_642, c_480])).
% 3.40/1.57  tff(c_1346, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_952, c_882])).
% 3.40/1.57  tff(c_1435, plain, (k5_xboole_0('#skF_3', '#skF_2')='#skF_2' | k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1429, c_1346])).
% 3.40/1.57  tff(c_1457, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_392, c_952, c_1435])).
% 3.40/1.57  tff(c_1458, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_1457])).
% 3.40/1.57  tff(c_1047, plain, (k5_xboole_0('#skF_2', '#skF_3')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_958, c_8])).
% 3.40/1.57  tff(c_959, plain, (![A_124, B_125]: (k5_xboole_0(A_124, k5_xboole_0(B_125, A_124))=B_125)), inference(superposition, [status(thm), theory('equality')], [c_2, c_883])).
% 3.40/1.57  tff(c_995, plain, (![A_18, C_103]: (k5_xboole_0(k5_xboole_0(A_18, C_103), C_103)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_882, c_959])).
% 3.40/1.57  tff(c_1301, plain, (k5_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1047, c_995])).
% 3.40/1.57  tff(c_1469, plain, (k5_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1301])).
% 3.40/1.57  tff(c_22, plain, (![A_19, B_20]: (k5_xboole_0(k5_xboole_0(A_19, B_20), k2_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.57  tff(c_1527, plain, (k5_xboole_0('#skF_2', k2_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1469, c_22])).
% 3.40/1.57  tff(c_1547, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_958, c_20, c_392, c_1527])).
% 3.40/1.57  tff(c_1549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1547])).
% 3.40/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.57  
% 3.40/1.57  Inference rules
% 3.40/1.57  ----------------------
% 3.40/1.57  #Ref     : 0
% 3.40/1.57  #Sup     : 373
% 3.40/1.57  #Fact    : 0
% 3.40/1.57  #Define  : 0
% 3.40/1.57  #Split   : 0
% 3.40/1.57  #Chain   : 0
% 3.40/1.57  #Close   : 0
% 3.40/1.57  
% 3.40/1.57  Ordering : KBO
% 3.40/1.57  
% 3.40/1.57  Simplification rules
% 3.40/1.57  ----------------------
% 3.40/1.57  #Subsume      : 6
% 3.40/1.57  #Demod        : 176
% 3.40/1.57  #Tautology    : 233
% 3.40/1.57  #SimpNegUnit  : 13
% 3.40/1.57  #BackRed      : 8
% 3.40/1.57  
% 3.40/1.57  #Partial instantiations: 0
% 3.40/1.57  #Strategies tried      : 1
% 3.40/1.57  
% 3.40/1.57  Timing (in seconds)
% 3.40/1.57  ----------------------
% 3.40/1.57  Preprocessing        : 0.35
% 3.40/1.57  Parsing              : 0.19
% 3.40/1.58  CNF conversion       : 0.02
% 3.40/1.58  Main loop            : 0.42
% 3.40/1.58  Inferencing          : 0.15
% 3.40/1.58  Reduction            : 0.16
% 3.40/1.58  Demodulation         : 0.13
% 3.40/1.58  BG Simplification    : 0.02
% 3.40/1.58  Subsumption          : 0.06
% 3.40/1.58  Abstraction          : 0.02
% 3.40/1.58  MUC search           : 0.00
% 3.40/1.58  Cooper               : 0.00
% 3.40/1.58  Total                : 0.80
% 3.40/1.58  Index Insertion      : 0.00
% 3.40/1.58  Index Deletion       : 0.00
% 3.40/1.58  Index Matching       : 0.00
% 3.40/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
