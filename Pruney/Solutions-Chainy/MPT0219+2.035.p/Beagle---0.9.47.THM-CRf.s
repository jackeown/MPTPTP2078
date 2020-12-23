%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:54 EST 2020

% Result     : Theorem 6.87s
% Output     : CNFRefutation 7.28s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 227 expanded)
%              Number of leaves         :   33 (  89 expanded)
%              Depth                    :   18
%              Number of atoms          :   67 ( 237 expanded)
%              Number of equality atoms :   54 ( 186 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_42,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_239,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1056,plain,(
    ! [A_130,B_131] : k3_xboole_0(k4_xboole_0(A_130,B_131),A_130) = k4_xboole_0(A_130,B_131) ),
    inference(resolution,[status(thm)],[c_16,c_239])).

tff(c_266,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_286,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_266])).

tff(c_5168,plain,(
    ! [A_188,B_189] : k5_xboole_0(A_188,k4_xboole_0(A_188,B_189)) = k4_xboole_0(A_188,k4_xboole_0(A_188,B_189)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1056,c_286])).

tff(c_24,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5226,plain,(
    ! [B_189] : k4_xboole_0(B_189,k4_xboole_0(B_189,B_189)) = k2_xboole_0(B_189,B_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_5168,c_24])).

tff(c_5286,plain,(
    ! [B_190] : k4_xboole_0(B_190,k4_xboole_0(B_190,B_190)) = B_190 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5226])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k4_xboole_0(B_18,A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5314,plain,(
    ! [B_190] :
      ( k4_xboole_0(B_190,B_190) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(B_190,B_190),B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5286,c_18])).

tff(c_5342,plain,(
    ! [B_190] : k4_xboole_0(B_190,B_190) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5314])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_289,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_266])).

tff(c_5635,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5342,c_289])).

tff(c_44,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_457,plain,(
    ! [A_91,B_92,C_93] : k5_xboole_0(k5_xboole_0(A_91,B_92),C_93) = k5_xboole_0(A_91,k5_xboole_0(B_92,C_93)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1677,plain,(
    ! [C_145,A_146,B_147] : k5_xboole_0(C_145,k5_xboole_0(A_146,B_147)) = k5_xboole_0(A_146,k5_xboole_0(B_147,C_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_4])).

tff(c_1831,plain,(
    ! [A_7,A_146] : k5_xboole_0(A_7,k5_xboole_0(A_146,A_7)) = k5_xboole_0(A_146,k4_xboole_0(A_7,A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_1677])).

tff(c_5632,plain,(
    ! [A_7,A_146] : k5_xboole_0(A_7,k5_xboole_0(A_146,A_7)) = k5_xboole_0(A_146,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5342,c_1831])).

tff(c_6351,plain,(
    ! [A_200,A_201] : k5_xboole_0(A_200,k5_xboole_0(A_201,A_200)) = A_201 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5632])).

tff(c_7398,plain,(
    ! [B_209,A_210] : k5_xboole_0(k4_xboole_0(B_209,A_210),k2_xboole_0(A_210,B_209)) = A_210 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6351])).

tff(c_7491,plain,(
    k5_xboole_0(k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')),k1_tarski('#skF_1')) = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_7398])).

tff(c_144,plain,(
    ! [B_68,A_69] : k5_xboole_0(B_68,A_69) = k5_xboole_0(A_69,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_160,plain,(
    ! [A_69] : k5_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_20])).

tff(c_501,plain,(
    ! [A_7,C_93] : k5_xboole_0(k4_xboole_0(A_7,A_7),C_93) = k5_xboole_0(A_7,k5_xboole_0(A_7,C_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_457])).

tff(c_5634,plain,(
    ! [A_7,C_93] : k5_xboole_0(A_7,k5_xboole_0(A_7,C_93)) = k5_xboole_0(k1_xboole_0,C_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5342,c_501])).

tff(c_5639,plain,(
    ! [A_7,C_93] : k5_xboole_0(A_7,k5_xboole_0(A_7,C_93)) = C_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_5634])).

tff(c_6442,plain,(
    ! [A_7,C_93] : k5_xboole_0(k5_xboole_0(A_7,C_93),C_93) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_5639,c_6351])).

tff(c_8067,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) = k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7491,c_6442])).

tff(c_8127,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5635,c_8067])).

tff(c_10,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6535,plain,(
    ! [A_9,B_10] : k5_xboole_0(k3_xboole_0(A_9,B_10),k4_xboole_0(A_9,B_10)) = A_9 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_6351])).

tff(c_8227,plain,(
    k5_xboole_0(k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')),k1_xboole_0) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8127,c_6535])).

tff(c_8259,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2,c_8227])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8433,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8259,c_12])).

tff(c_40,plain,(
    ! [B_54,A_53] :
      ( B_54 = A_53
      | ~ r1_tarski(k1_tarski(A_53),k1_tarski(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8461,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_8433,c_40])).

tff(c_8466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_8461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:25:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.87/2.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.81  
% 6.87/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.81  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.87/2.81  
% 6.87/2.81  %Foreground sorts:
% 6.87/2.81  
% 6.87/2.81  
% 6.87/2.81  %Background operators:
% 6.87/2.81  
% 6.87/2.81  
% 6.87/2.81  %Foreground operators:
% 6.87/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.87/2.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.87/2.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.87/2.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.87/2.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.87/2.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.87/2.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.87/2.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.87/2.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.87/2.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.87/2.81  tff('#skF_2', type, '#skF_2': $i).
% 6.87/2.81  tff('#skF_1', type, '#skF_1': $i).
% 6.87/2.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.87/2.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.87/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.87/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.87/2.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.87/2.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.87/2.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.87/2.81  
% 7.28/2.82  tff(f_76, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 7.28/2.82  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.28/2.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.28/2.82  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.28/2.82  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.28/2.82  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.28/2.82  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.28/2.82  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.28/2.82  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 7.28/2.82  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.28/2.82  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.28/2.82  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.28/2.82  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.28/2.82  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 7.28/2.82  tff(c_42, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.28/2.82  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.28/2.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.28/2.82  tff(c_16, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.28/2.82  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.28/2.82  tff(c_239, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.28/2.82  tff(c_1056, plain, (![A_130, B_131]: (k3_xboole_0(k4_xboole_0(A_130, B_131), A_130)=k4_xboole_0(A_130, B_131))), inference(resolution, [status(thm)], [c_16, c_239])).
% 7.28/2.82  tff(c_266, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.28/2.82  tff(c_286, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_266])).
% 7.28/2.82  tff(c_5168, plain, (![A_188, B_189]: (k5_xboole_0(A_188, k4_xboole_0(A_188, B_189))=k4_xboole_0(A_188, k4_xboole_0(A_188, B_189)))), inference(superposition, [status(thm), theory('equality')], [c_1056, c_286])).
% 7.28/2.82  tff(c_24, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.28/2.82  tff(c_5226, plain, (![B_189]: (k4_xboole_0(B_189, k4_xboole_0(B_189, B_189))=k2_xboole_0(B_189, B_189))), inference(superposition, [status(thm), theory('equality')], [c_5168, c_24])).
% 7.28/2.82  tff(c_5286, plain, (![B_190]: (k4_xboole_0(B_190, k4_xboole_0(B_190, B_190))=B_190)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5226])).
% 7.28/2.82  tff(c_18, plain, (![A_17, B_18]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k4_xboole_0(B_18, A_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.28/2.82  tff(c_5314, plain, (![B_190]: (k4_xboole_0(B_190, B_190)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(B_190, B_190), B_190))), inference(superposition, [status(thm), theory('equality')], [c_5286, c_18])).
% 7.28/2.82  tff(c_5342, plain, (![B_190]: (k4_xboole_0(B_190, B_190)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5314])).
% 7.28/2.82  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.28/2.82  tff(c_289, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_266])).
% 7.28/2.82  tff(c_5635, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5342, c_289])).
% 7.28/2.82  tff(c_44, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.28/2.82  tff(c_457, plain, (![A_91, B_92, C_93]: (k5_xboole_0(k5_xboole_0(A_91, B_92), C_93)=k5_xboole_0(A_91, k5_xboole_0(B_92, C_93)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.28/2.82  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.28/2.82  tff(c_1677, plain, (![C_145, A_146, B_147]: (k5_xboole_0(C_145, k5_xboole_0(A_146, B_147))=k5_xboole_0(A_146, k5_xboole_0(B_147, C_145)))), inference(superposition, [status(thm), theory('equality')], [c_457, c_4])).
% 7.28/2.82  tff(c_1831, plain, (![A_7, A_146]: (k5_xboole_0(A_7, k5_xboole_0(A_146, A_7))=k5_xboole_0(A_146, k4_xboole_0(A_7, A_7)))), inference(superposition, [status(thm), theory('equality')], [c_289, c_1677])).
% 7.28/2.82  tff(c_5632, plain, (![A_7, A_146]: (k5_xboole_0(A_7, k5_xboole_0(A_146, A_7))=k5_xboole_0(A_146, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5342, c_1831])).
% 7.28/2.82  tff(c_6351, plain, (![A_200, A_201]: (k5_xboole_0(A_200, k5_xboole_0(A_201, A_200))=A_201)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5632])).
% 7.28/2.82  tff(c_7398, plain, (![B_209, A_210]: (k5_xboole_0(k4_xboole_0(B_209, A_210), k2_xboole_0(A_210, B_209))=A_210)), inference(superposition, [status(thm), theory('equality')], [c_24, c_6351])).
% 7.28/2.82  tff(c_7491, plain, (k5_xboole_0(k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1')), k1_tarski('#skF_1'))=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_44, c_7398])).
% 7.28/2.82  tff(c_144, plain, (![B_68, A_69]: (k5_xboole_0(B_68, A_69)=k5_xboole_0(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.28/2.82  tff(c_160, plain, (![A_69]: (k5_xboole_0(k1_xboole_0, A_69)=A_69)), inference(superposition, [status(thm), theory('equality')], [c_144, c_20])).
% 7.28/2.82  tff(c_501, plain, (![A_7, C_93]: (k5_xboole_0(k4_xboole_0(A_7, A_7), C_93)=k5_xboole_0(A_7, k5_xboole_0(A_7, C_93)))), inference(superposition, [status(thm), theory('equality')], [c_289, c_457])).
% 7.28/2.82  tff(c_5634, plain, (![A_7, C_93]: (k5_xboole_0(A_7, k5_xboole_0(A_7, C_93))=k5_xboole_0(k1_xboole_0, C_93))), inference(demodulation, [status(thm), theory('equality')], [c_5342, c_501])).
% 7.28/2.82  tff(c_5639, plain, (![A_7, C_93]: (k5_xboole_0(A_7, k5_xboole_0(A_7, C_93))=C_93)), inference(demodulation, [status(thm), theory('equality')], [c_160, c_5634])).
% 7.28/2.82  tff(c_6442, plain, (![A_7, C_93]: (k5_xboole_0(k5_xboole_0(A_7, C_93), C_93)=A_7)), inference(superposition, [status(thm), theory('equality')], [c_5639, c_6351])).
% 7.28/2.82  tff(c_8067, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))=k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7491, c_6442])).
% 7.28/2.82  tff(c_8127, plain, (k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5635, c_8067])).
% 7.28/2.82  tff(c_10, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.28/2.82  tff(c_6535, plain, (![A_9, B_10]: (k5_xboole_0(k3_xboole_0(A_9, B_10), k4_xboole_0(A_9, B_10))=A_9)), inference(superposition, [status(thm), theory('equality')], [c_10, c_6351])).
% 7.28/2.82  tff(c_8227, plain, (k5_xboole_0(k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1')), k1_xboole_0)=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8127, c_6535])).
% 7.28/2.82  tff(c_8259, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2, c_8227])).
% 7.28/2.82  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.28/2.82  tff(c_8433, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8259, c_12])).
% 7.28/2.82  tff(c_40, plain, (![B_54, A_53]: (B_54=A_53 | ~r1_tarski(k1_tarski(A_53), k1_tarski(B_54)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.28/2.82  tff(c_8461, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_8433, c_40])).
% 7.28/2.82  tff(c_8466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_8461])).
% 7.28/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.28/2.82  
% 7.28/2.82  Inference rules
% 7.28/2.82  ----------------------
% 7.28/2.82  #Ref     : 0
% 7.28/2.82  #Sup     : 2083
% 7.28/2.82  #Fact    : 0
% 7.28/2.82  #Define  : 0
% 7.28/2.82  #Split   : 0
% 7.28/2.82  #Chain   : 0
% 7.28/2.82  #Close   : 0
% 7.28/2.82  
% 7.28/2.82  Ordering : KBO
% 7.28/2.82  
% 7.28/2.82  Simplification rules
% 7.28/2.82  ----------------------
% 7.28/2.82  #Subsume      : 107
% 7.28/2.82  #Demod        : 1951
% 7.28/2.82  #Tautology    : 1023
% 7.28/2.82  #SimpNegUnit  : 1
% 7.28/2.82  #BackRed      : 14
% 7.28/2.82  
% 7.28/2.82  #Partial instantiations: 0
% 7.28/2.82  #Strategies tried      : 1
% 7.28/2.82  
% 7.28/2.82  Timing (in seconds)
% 7.28/2.82  ----------------------
% 7.28/2.83  Preprocessing        : 0.33
% 7.28/2.83  Parsing              : 0.17
% 7.28/2.83  CNF conversion       : 0.02
% 7.28/2.83  Main loop            : 1.72
% 7.28/2.83  Inferencing          : 0.43
% 7.28/2.83  Reduction            : 0.97
% 7.28/2.83  Demodulation         : 0.86
% 7.28/2.83  BG Simplification    : 0.06
% 7.28/2.83  Subsumption          : 0.19
% 7.28/2.83  Abstraction          : 0.10
% 7.28/2.83  MUC search           : 0.00
% 7.28/2.83  Cooper               : 0.00
% 7.28/2.83  Total                : 2.08
% 7.28/2.83  Index Insertion      : 0.00
% 7.28/2.83  Index Deletion       : 0.00
% 7.28/2.83  Index Matching       : 0.00
% 7.28/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
