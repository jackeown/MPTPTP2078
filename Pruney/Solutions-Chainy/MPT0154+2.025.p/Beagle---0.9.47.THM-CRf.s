%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:07 EST 2020

% Result     : Theorem 6.72s
% Output     : CNFRefutation 6.72s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 288 expanded)
%              Number of leaves         :   27 ( 106 expanded)
%              Depth                    :   18
%              Number of atoms          :   59 ( 276 expanded)
%              Number of equality atoms :   54 ( 271 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k1_tarski(A_22),k2_tarski(B_23,C_24)) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_191,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k4_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_191])).

tff(c_219,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_215])).

tff(c_376,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_405,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_376])).

tff(c_411,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_405])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_212,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_191])).

tff(c_412,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_212])).

tff(c_284,plain,(
    ! [A_47,B_48] : k2_xboole_0(k1_tarski(A_47),k1_tarski(B_48)) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_167,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(resolution,[status(thm)],[c_16,c_167])).

tff(c_680,plain,(
    ! [A_71,B_72] : k3_xboole_0(k1_tarski(A_71),k2_tarski(A_71,B_72)) = k1_tarski(A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_171])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_689,plain,(
    ! [A_71,B_72] : k5_xboole_0(k1_tarski(A_71),k1_tarski(A_71)) = k4_xboole_0(k1_tarski(A_71),k2_tarski(A_71,B_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_6])).

tff(c_697,plain,(
    ! [A_71,B_72] : k4_xboole_0(k1_tarski(A_71),k2_tarski(A_71,B_72)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_689])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_209,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_534,plain,(
    ! [A_64,B_65,C_66] : k5_xboole_0(k5_xboole_0(A_64,B_65),C_66) = k5_xboole_0(A_64,k5_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1522,plain,(
    ! [A_99,B_100,C_101] : k5_xboole_0(A_99,k5_xboole_0(k3_xboole_0(A_99,B_100),C_101)) = k5_xboole_0(k4_xboole_0(A_99,B_100),C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_534])).

tff(c_1591,plain,(
    ! [A_99,B_100] : k5_xboole_0(k4_xboole_0(A_99,B_100),k3_xboole_0(A_99,B_100)) = k5_xboole_0(A_99,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_1522])).

tff(c_1964,plain,(
    ! [A_108,B_109] : k5_xboole_0(k4_xboole_0(A_108,B_109),k3_xboole_0(A_108,B_109)) = A_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1591])).

tff(c_229,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k4_xboole_0(B_43,A_42)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_238,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = k2_xboole_0(k1_xboole_0,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_229])).

tff(c_565,plain,(
    ! [A_3,C_66] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_66)) = k5_xboole_0(k1_xboole_0,C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_534])).

tff(c_1030,plain,(
    ! [A_85,C_86] : k5_xboole_0(A_85,k5_xboole_0(A_85,C_86)) = k2_xboole_0(k1_xboole_0,C_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_565])).

tff(c_1090,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_1030])).

tff(c_1121,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1090])).

tff(c_599,plain,(
    ! [A_3,C_66] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_66)) = k2_xboole_0(k1_xboole_0,C_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_565])).

tff(c_1124,plain,(
    ! [A_3,C_66] : k5_xboole_0(A_3,k5_xboole_0(A_3,C_66)) = C_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_599])).

tff(c_4630,plain,(
    ! [A_165,B_166] : k5_xboole_0(k4_xboole_0(A_165,B_166),A_165) = k3_xboole_0(A_165,B_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_1964,c_1124])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_575,plain,(
    ! [A_18,B_19,C_66] : k5_xboole_0(A_18,k5_xboole_0(k4_xboole_0(B_19,A_18),C_66)) = k5_xboole_0(k2_xboole_0(A_18,B_19),C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_534])).

tff(c_4645,plain,(
    ! [B_166,A_165] : k5_xboole_0(k2_xboole_0(B_166,A_165),A_165) = k5_xboole_0(B_166,k3_xboole_0(A_165,B_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4630,c_575])).

tff(c_7141,plain,(
    ! [B_202,A_203] : k5_xboole_0(k2_xboole_0(B_202,A_203),A_203) = k4_xboole_0(B_202,A_203) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_4645])).

tff(c_11122,plain,(
    ! [B_248,A_249] : k5_xboole_0(k2_xboole_0(B_248,A_249),k4_xboole_0(B_248,A_249)) = A_249 ),
    inference(superposition,[status(thm),theory(equality)],[c_7141,c_1124])).

tff(c_11238,plain,(
    ! [A_71,B_72] : k5_xboole_0(k2_xboole_0(k1_tarski(A_71),k2_tarski(A_71,B_72)),k1_xboole_0) = k2_tarski(A_71,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_11122])).

tff(c_11294,plain,(
    ! [A_71,B_72] : k1_enumset1(A_71,A_71,B_72) = k2_tarski(A_71,B_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24,c_11238])).

tff(c_28,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_11303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11294,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.72/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.72/2.48  
% 6.72/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.72/2.48  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.72/2.48  
% 6.72/2.48  %Foreground sorts:
% 6.72/2.48  
% 6.72/2.48  
% 6.72/2.48  %Background operators:
% 6.72/2.48  
% 6.72/2.48  
% 6.72/2.48  %Foreground operators:
% 6.72/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.72/2.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.72/2.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.72/2.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.72/2.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.72/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.72/2.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.72/2.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.72/2.48  tff('#skF_2', type, '#skF_2': $i).
% 6.72/2.48  tff('#skF_1', type, '#skF_1': $i).
% 6.72/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.72/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.72/2.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.72/2.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.72/2.48  
% 6.72/2.50  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.72/2.50  tff(f_51, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 6.72/2.50  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 6.72/2.50  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.72/2.50  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.72/2.50  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.72/2.50  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 6.72/2.50  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.72/2.50  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.72/2.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.72/2.50  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.72/2.50  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.72/2.50  tff(f_56, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.72/2.50  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.72/2.50  tff(c_24, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k1_tarski(A_22), k2_tarski(B_23, C_24))=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.72/2.50  tff(c_10, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.72/2.50  tff(c_191, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.72/2.50  tff(c_215, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k4_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_191])).
% 6.72/2.50  tff(c_219, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_215])).
% 6.72/2.50  tff(c_376, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.72/2.50  tff(c_405, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_219, c_376])).
% 6.72/2.50  tff(c_411, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_405])).
% 6.72/2.50  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.72/2.50  tff(c_212, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_191])).
% 6.72/2.50  tff(c_412, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_411, c_212])).
% 6.72/2.50  tff(c_284, plain, (![A_47, B_48]: (k2_xboole_0(k1_tarski(A_47), k1_tarski(B_48))=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.72/2.50  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.72/2.50  tff(c_167, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.72/2.50  tff(c_171, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(resolution, [status(thm)], [c_16, c_167])).
% 6.72/2.50  tff(c_680, plain, (![A_71, B_72]: (k3_xboole_0(k1_tarski(A_71), k2_tarski(A_71, B_72))=k1_tarski(A_71))), inference(superposition, [status(thm), theory('equality')], [c_284, c_171])).
% 6.72/2.50  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.72/2.50  tff(c_689, plain, (![A_71, B_72]: (k5_xboole_0(k1_tarski(A_71), k1_tarski(A_71))=k4_xboole_0(k1_tarski(A_71), k2_tarski(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_680, c_6])).
% 6.72/2.50  tff(c_697, plain, (![A_71, B_72]: (k4_xboole_0(k1_tarski(A_71), k2_tarski(A_71, B_72))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_412, c_689])).
% 6.72/2.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.72/2.50  tff(c_209, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_191])).
% 6.72/2.50  tff(c_534, plain, (![A_64, B_65, C_66]: (k5_xboole_0(k5_xboole_0(A_64, B_65), C_66)=k5_xboole_0(A_64, k5_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.72/2.50  tff(c_1522, plain, (![A_99, B_100, C_101]: (k5_xboole_0(A_99, k5_xboole_0(k3_xboole_0(A_99, B_100), C_101))=k5_xboole_0(k4_xboole_0(A_99, B_100), C_101))), inference(superposition, [status(thm), theory('equality')], [c_6, c_534])).
% 6.72/2.50  tff(c_1591, plain, (![A_99, B_100]: (k5_xboole_0(k4_xboole_0(A_99, B_100), k3_xboole_0(A_99, B_100))=k5_xboole_0(A_99, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_412, c_1522])).
% 6.72/2.50  tff(c_1964, plain, (![A_108, B_109]: (k5_xboole_0(k4_xboole_0(A_108, B_109), k3_xboole_0(A_108, B_109))=A_108)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1591])).
% 6.72/2.50  tff(c_229, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k4_xboole_0(B_43, A_42))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.72/2.50  tff(c_238, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=k2_xboole_0(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_219, c_229])).
% 6.72/2.50  tff(c_565, plain, (![A_3, C_66]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_66))=k5_xboole_0(k1_xboole_0, C_66))), inference(superposition, [status(thm), theory('equality')], [c_412, c_534])).
% 6.72/2.50  tff(c_1030, plain, (![A_85, C_86]: (k5_xboole_0(A_85, k5_xboole_0(A_85, C_86))=k2_xboole_0(k1_xboole_0, C_86))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_565])).
% 6.72/2.50  tff(c_1090, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_412, c_1030])).
% 6.72/2.50  tff(c_1121, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1090])).
% 6.72/2.50  tff(c_599, plain, (![A_3, C_66]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_66))=k2_xboole_0(k1_xboole_0, C_66))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_565])).
% 6.72/2.50  tff(c_1124, plain, (![A_3, C_66]: (k5_xboole_0(A_3, k5_xboole_0(A_3, C_66))=C_66)), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_599])).
% 6.72/2.50  tff(c_4630, plain, (![A_165, B_166]: (k5_xboole_0(k4_xboole_0(A_165, B_166), A_165)=k3_xboole_0(A_165, B_166))), inference(superposition, [status(thm), theory('equality')], [c_1964, c_1124])).
% 6.72/2.50  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.72/2.50  tff(c_575, plain, (![A_18, B_19, C_66]: (k5_xboole_0(A_18, k5_xboole_0(k4_xboole_0(B_19, A_18), C_66))=k5_xboole_0(k2_xboole_0(A_18, B_19), C_66))), inference(superposition, [status(thm), theory('equality')], [c_20, c_534])).
% 6.72/2.50  tff(c_4645, plain, (![B_166, A_165]: (k5_xboole_0(k2_xboole_0(B_166, A_165), A_165)=k5_xboole_0(B_166, k3_xboole_0(A_165, B_166)))), inference(superposition, [status(thm), theory('equality')], [c_4630, c_575])).
% 6.72/2.50  tff(c_7141, plain, (![B_202, A_203]: (k5_xboole_0(k2_xboole_0(B_202, A_203), A_203)=k4_xboole_0(B_202, A_203))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_4645])).
% 6.72/2.50  tff(c_11122, plain, (![B_248, A_249]: (k5_xboole_0(k2_xboole_0(B_248, A_249), k4_xboole_0(B_248, A_249))=A_249)), inference(superposition, [status(thm), theory('equality')], [c_7141, c_1124])).
% 6.72/2.50  tff(c_11238, plain, (![A_71, B_72]: (k5_xboole_0(k2_xboole_0(k1_tarski(A_71), k2_tarski(A_71, B_72)), k1_xboole_0)=k2_tarski(A_71, B_72))), inference(superposition, [status(thm), theory('equality')], [c_697, c_11122])).
% 6.72/2.50  tff(c_11294, plain, (![A_71, B_72]: (k1_enumset1(A_71, A_71, B_72)=k2_tarski(A_71, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24, c_11238])).
% 6.72/2.50  tff(c_28, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.72/2.50  tff(c_11303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11294, c_28])).
% 6.72/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.72/2.50  
% 6.72/2.50  Inference rules
% 6.72/2.50  ----------------------
% 6.72/2.50  #Ref     : 0
% 6.72/2.50  #Sup     : 2782
% 6.72/2.50  #Fact    : 0
% 6.72/2.50  #Define  : 0
% 6.72/2.50  #Split   : 0
% 6.72/2.50  #Chain   : 0
% 6.72/2.50  #Close   : 0
% 6.72/2.50  
% 6.72/2.50  Ordering : KBO
% 6.72/2.50  
% 6.72/2.50  Simplification rules
% 6.72/2.50  ----------------------
% 6.72/2.50  #Subsume      : 42
% 6.72/2.50  #Demod        : 3432
% 6.72/2.50  #Tautology    : 1986
% 6.72/2.50  #SimpNegUnit  : 0
% 6.72/2.50  #BackRed      : 7
% 6.72/2.50  
% 6.72/2.50  #Partial instantiations: 0
% 6.72/2.50  #Strategies tried      : 1
% 6.72/2.50  
% 6.72/2.50  Timing (in seconds)
% 6.72/2.50  ----------------------
% 6.72/2.50  Preprocessing        : 0.28
% 6.72/2.50  Parsing              : 0.15
% 6.72/2.50  CNF conversion       : 0.01
% 6.72/2.50  Main loop            : 1.45
% 6.72/2.50  Inferencing          : 0.41
% 6.72/2.50  Reduction            : 0.74
% 6.72/2.50  Demodulation         : 0.64
% 6.72/2.50  BG Simplification    : 0.04
% 6.72/2.50  Subsumption          : 0.18
% 6.72/2.50  Abstraction          : 0.08
% 6.72/2.50  MUC search           : 0.00
% 6.72/2.50  Cooper               : 0.00
% 6.72/2.50  Total                : 1.76
% 6.72/2.50  Index Insertion      : 0.00
% 6.72/2.50  Index Deletion       : 0.00
% 6.72/2.50  Index Matching       : 0.00
% 6.72/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
