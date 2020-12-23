%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:33 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 700 expanded)
%              Number of leaves         :   30 ( 248 expanded)
%              Depth                    :   14
%              Number of atoms          :   62 ( 682 expanded)
%              Number of equality atoms :   61 ( 681 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_89,plain,(
    ! [B_54,A_55] : k5_xboole_0(B_54,A_55) = k5_xboole_0(A_55,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_105,plain,(
    ! [A_55] : k5_xboole_0(k1_xboole_0,A_55) = A_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_12])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_729,plain,(
    ! [A_89,B_90,C_91] : k5_xboole_0(k5_xboole_0(A_89,B_90),C_91) = k5_xboole_0(A_89,k5_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_817,plain,(
    ! [A_15,C_91] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_91)) = k5_xboole_0(k1_xboole_0,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_729])).

tff(c_832,plain,(
    ! [A_15,C_91] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_91)) = C_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_817])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_883,plain,(
    ! [A_94,C_95] : k5_xboole_0(A_94,k5_xboole_0(A_94,C_95)) = C_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_817])).

tff(c_966,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k5_xboole_0(B_101,A_100)) = B_101 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_883])).

tff(c_1002,plain,(
    ! [A_15,C_91] : k5_xboole_0(k5_xboole_0(A_15,C_91),C_91) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_966])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_258,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_271,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_258])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(k5_xboole_0(A_16,B_17),k3_xboole_0(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_742,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k5_xboole_0(B_90,k3_xboole_0(A_89,B_90))) = k2_xboole_0(A_89,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_729,c_18])).

tff(c_1309,plain,(
    ! [A_117,B_118] : k5_xboole_0(A_117,k4_xboole_0(B_118,A_117)) = k2_xboole_0(A_117,B_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_742])).

tff(c_1540,plain,(
    ! [A_130,B_131] : k5_xboole_0(A_130,k2_xboole_0(A_130,B_131)) = k4_xboole_0(B_131,A_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_1309,c_832])).

tff(c_1592,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k4_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1540])).

tff(c_1601,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1592])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1614,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) = k3_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1601,c_10])).

tff(c_1619,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1601,c_1614])).

tff(c_1681,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) = k2_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1619,c_18])).

tff(c_1691,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_1681])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_925,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_883])).

tff(c_1608,plain,(
    k5_xboole_0('#skF_2',k1_tarski('#skF_1')) = k3_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1601,c_925])).

tff(c_1723,plain,(
    k5_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1619,c_1608])).

tff(c_1742,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k3_xboole_0('#skF_2',k1_tarski('#skF_1'))) = k2_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1723,c_18])).

tff(c_1746,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1691,c_16,c_1619,c_1742])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_281,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_258])).

tff(c_284,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_281])).

tff(c_36,plain,(
    ! [B_49] : k4_xboole_0(k1_tarski(B_49),k1_tarski(B_49)) != k1_tarski(B_49) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_285,plain,(
    ! [B_49] : k1_tarski(B_49) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_36])).

tff(c_1756,plain,(
    ! [B_49] : k1_tarski(B_49) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1746,c_285])).

tff(c_313,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k4_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_339,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = k3_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_313])).

tff(c_345,plain,(
    ! [A_72] : k4_xboole_0(A_72,k1_xboole_0) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_339])).

tff(c_351,plain,(
    ! [A_72] : k4_xboole_0(A_72,A_72) = k3_xboole_0(A_72,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_10])).

tff(c_378,plain,(
    ! [A_73] : k3_xboole_0(A_73,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_351])).

tff(c_386,plain,(
    ! [A_73] : k3_xboole_0(k1_xboole_0,A_73) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_2])).

tff(c_634,plain,(
    ! [A_85,B_86] : k5_xboole_0(k5_xboole_0(A_85,B_86),k3_xboole_0(A_85,B_86)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_676,plain,(
    ! [A_55] : k5_xboole_0(A_55,k3_xboole_0(k1_xboole_0,A_55)) = k2_xboole_0(k1_xboole_0,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_634])).

tff(c_705,plain,(
    ! [A_55] : k2_xboole_0(k1_xboole_0,A_55) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_386,c_676])).

tff(c_1767,plain,(
    ! [A_135] : k2_xboole_0('#skF_2',A_135) = A_135 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1746,c_705])).

tff(c_1773,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1767,c_1691])).

tff(c_1793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1756,c_1773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:32:35 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.55  
% 3.34/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.56  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.34/1.56  
% 3.34/1.56  %Foreground sorts:
% 3.34/1.56  
% 3.34/1.56  
% 3.34/1.56  %Background operators:
% 3.34/1.56  
% 3.34/1.56  
% 3.34/1.56  %Foreground operators:
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.34/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.34/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.34/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.34/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.56  
% 3.34/1.57  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.34/1.57  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.34/1.57  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.34/1.57  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.34/1.57  tff(f_68, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.34/1.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.34/1.57  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.34/1.57  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.34/1.57  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.34/1.57  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.34/1.57  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.34/1.57  tff(c_89, plain, (![B_54, A_55]: (k5_xboole_0(B_54, A_55)=k5_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.57  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.57  tff(c_105, plain, (![A_55]: (k5_xboole_0(k1_xboole_0, A_55)=A_55)), inference(superposition, [status(thm), theory('equality')], [c_89, c_12])).
% 3.34/1.57  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.34/1.57  tff(c_729, plain, (![A_89, B_90, C_91]: (k5_xboole_0(k5_xboole_0(A_89, B_90), C_91)=k5_xboole_0(A_89, k5_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.57  tff(c_817, plain, (![A_15, C_91]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_91))=k5_xboole_0(k1_xboole_0, C_91))), inference(superposition, [status(thm), theory('equality')], [c_16, c_729])).
% 3.34/1.57  tff(c_832, plain, (![A_15, C_91]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_91))=C_91)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_817])).
% 3.34/1.57  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.57  tff(c_883, plain, (![A_94, C_95]: (k5_xboole_0(A_94, k5_xboole_0(A_94, C_95))=C_95)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_817])).
% 3.34/1.57  tff(c_966, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k5_xboole_0(B_101, A_100))=B_101)), inference(superposition, [status(thm), theory('equality')], [c_4, c_883])).
% 3.34/1.57  tff(c_1002, plain, (![A_15, C_91]: (k5_xboole_0(k5_xboole_0(A_15, C_91), C_91)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_832, c_966])).
% 3.34/1.57  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.34/1.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.57  tff(c_258, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.34/1.57  tff(c_271, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_258])).
% 3.34/1.57  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(k5_xboole_0(A_16, B_17), k3_xboole_0(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.57  tff(c_742, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k5_xboole_0(B_90, k3_xboole_0(A_89, B_90)))=k2_xboole_0(A_89, B_90))), inference(superposition, [status(thm), theory('equality')], [c_729, c_18])).
% 3.34/1.57  tff(c_1309, plain, (![A_117, B_118]: (k5_xboole_0(A_117, k4_xboole_0(B_118, A_117))=k2_xboole_0(A_117, B_118))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_742])).
% 3.34/1.57  tff(c_1540, plain, (![A_130, B_131]: (k5_xboole_0(A_130, k2_xboole_0(A_130, B_131))=k4_xboole_0(B_131, A_130))), inference(superposition, [status(thm), theory('equality')], [c_1309, c_832])).
% 3.34/1.57  tff(c_1592, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k4_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1540])).
% 3.34/1.57  tff(c_1601, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1592])).
% 3.34/1.57  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.34/1.57  tff(c_1614, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))=k3_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1601, c_10])).
% 3.34/1.57  tff(c_1619, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1601, c_1614])).
% 3.34/1.57  tff(c_1681, plain, (k5_xboole_0(k5_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))=k2_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1619, c_18])).
% 3.34/1.57  tff(c_1691, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1002, c_1681])).
% 3.34/1.57  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.34/1.57  tff(c_925, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_883])).
% 3.34/1.57  tff(c_1608, plain, (k5_xboole_0('#skF_2', k1_tarski('#skF_1'))=k3_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1601, c_925])).
% 3.34/1.57  tff(c_1723, plain, (k5_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1619, c_1608])).
% 3.34/1.57  tff(c_1742, plain, (k5_xboole_0(k1_tarski('#skF_1'), k3_xboole_0('#skF_2', k1_tarski('#skF_1')))=k2_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1723, c_18])).
% 3.34/1.57  tff(c_1746, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1691, c_16, c_1619, c_1742])).
% 3.34/1.57  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.57  tff(c_281, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_258])).
% 3.34/1.57  tff(c_284, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_281])).
% 3.34/1.57  tff(c_36, plain, (![B_49]: (k4_xboole_0(k1_tarski(B_49), k1_tarski(B_49))!=k1_tarski(B_49))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.57  tff(c_285, plain, (![B_49]: (k1_tarski(B_49)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_284, c_36])).
% 3.34/1.57  tff(c_1756, plain, (![B_49]: (k1_tarski(B_49)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1746, c_285])).
% 3.34/1.57  tff(c_313, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k4_xboole_0(A_70, B_71))=k3_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.34/1.57  tff(c_339, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=k3_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_284, c_313])).
% 3.34/1.57  tff(c_345, plain, (![A_72]: (k4_xboole_0(A_72, k1_xboole_0)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_339])).
% 3.34/1.57  tff(c_351, plain, (![A_72]: (k4_xboole_0(A_72, A_72)=k3_xboole_0(A_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_345, c_10])).
% 3.34/1.57  tff(c_378, plain, (![A_73]: (k3_xboole_0(A_73, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_284, c_351])).
% 3.34/1.57  tff(c_386, plain, (![A_73]: (k3_xboole_0(k1_xboole_0, A_73)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_378, c_2])).
% 3.34/1.57  tff(c_634, plain, (![A_85, B_86]: (k5_xboole_0(k5_xboole_0(A_85, B_86), k3_xboole_0(A_85, B_86))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.57  tff(c_676, plain, (![A_55]: (k5_xboole_0(A_55, k3_xboole_0(k1_xboole_0, A_55))=k2_xboole_0(k1_xboole_0, A_55))), inference(superposition, [status(thm), theory('equality')], [c_105, c_634])).
% 3.34/1.57  tff(c_705, plain, (![A_55]: (k2_xboole_0(k1_xboole_0, A_55)=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_386, c_676])).
% 3.34/1.57  tff(c_1767, plain, (![A_135]: (k2_xboole_0('#skF_2', A_135)=A_135)), inference(demodulation, [status(thm), theory('equality')], [c_1746, c_705])).
% 3.34/1.57  tff(c_1773, plain, (k1_tarski('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1767, c_1691])).
% 3.34/1.57  tff(c_1793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1756, c_1773])).
% 3.34/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.57  
% 3.34/1.57  Inference rules
% 3.34/1.57  ----------------------
% 3.34/1.57  #Ref     : 0
% 3.34/1.57  #Sup     : 431
% 3.34/1.57  #Fact    : 0
% 3.34/1.57  #Define  : 0
% 3.34/1.57  #Split   : 0
% 3.34/1.57  #Chain   : 0
% 3.34/1.57  #Close   : 0
% 3.34/1.57  
% 3.34/1.57  Ordering : KBO
% 3.34/1.57  
% 3.34/1.57  Simplification rules
% 3.34/1.57  ----------------------
% 3.34/1.57  #Subsume      : 14
% 3.34/1.57  #Demod        : 263
% 3.34/1.57  #Tautology    : 283
% 3.34/1.57  #SimpNegUnit  : 5
% 3.34/1.57  #BackRed      : 17
% 3.34/1.57  
% 3.34/1.57  #Partial instantiations: 0
% 3.34/1.57  #Strategies tried      : 1
% 3.34/1.57  
% 3.34/1.57  Timing (in seconds)
% 3.34/1.57  ----------------------
% 3.34/1.57  Preprocessing        : 0.33
% 3.34/1.57  Parsing              : 0.18
% 3.34/1.57  CNF conversion       : 0.02
% 3.34/1.57  Main loop            : 0.45
% 3.34/1.57  Inferencing          : 0.16
% 3.34/1.57  Reduction            : 0.19
% 3.34/1.57  Demodulation         : 0.15
% 3.34/1.57  BG Simplification    : 0.02
% 3.34/1.57  Subsumption          : 0.06
% 3.34/1.57  Abstraction          : 0.03
% 3.34/1.57  MUC search           : 0.00
% 3.34/1.57  Cooper               : 0.00
% 3.34/1.57  Total                : 0.81
% 3.34/1.58  Index Insertion      : 0.00
% 3.34/1.58  Index Deletion       : 0.00
% 3.34/1.58  Index Matching       : 0.00
% 3.34/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
