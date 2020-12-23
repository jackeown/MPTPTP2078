%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:35 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 922 expanded)
%              Number of leaves         :   30 ( 324 expanded)
%              Depth                    :   17
%              Number of atoms          :   79 (1221 expanded)
%              Number of equality atoms :   59 ( 807 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_54,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k1_tarski(A_30),B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_269,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k1_xboole_0
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_283,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(k1_tarski(A_30),B_31) = k1_xboole_0
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_38,c_269])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_367,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_388,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_367])).

tff(c_26,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_890,plain,(
    ! [A_111,B_112,C_113] : k5_xboole_0(k5_xboole_0(A_111,B_112),C_113) = k5_xboole_0(A_111,k5_xboole_0(B_112,C_113)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_931,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k5_xboole_0(B_19,k3_xboole_0(A_18,B_19))) = k2_xboole_0(A_18,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_890])).

tff(c_1076,plain,(
    ! [A_120,B_121] : k5_xboole_0(A_120,k4_xboole_0(B_121,A_120)) = k2_xboole_0(A_120,B_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_931])).

tff(c_1110,plain,(
    ! [B_31,A_30] :
      ( k2_xboole_0(B_31,k1_tarski(A_30)) = k5_xboole_0(B_31,k1_xboole_0)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_1076])).

tff(c_1125,plain,(
    ! [B_31,A_30] :
      ( k2_xboole_0(B_31,k1_tarski(A_30)) = B_31
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1110])).

tff(c_966,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_931])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_284,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_269])).

tff(c_139,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = A_50
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_146,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_139])).

tff(c_382,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_367])).

tff(c_393,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_382])).

tff(c_911,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k5_xboole_0(B_112,k5_xboole_0(A_111,B_112))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_393])).

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,(
    ! [A_53] : k3_xboole_0(k1_xboole_0,A_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_139])).

tff(c_166,plain,(
    ! [A_53] : k3_xboole_0(A_53,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2])).

tff(c_797,plain,(
    ! [A_106,B_107] : k5_xboole_0(k5_xboole_0(A_106,B_107),k3_xboole_0(A_106,B_107)) = k2_xboole_0(A_106,B_107) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_839,plain,(
    ! [A_14] : k5_xboole_0(A_14,k3_xboole_0(A_14,k1_xboole_0)) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_797])).

tff(c_847,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_166,c_839])).

tff(c_441,plain,(
    ! [A_77,B_78] : k2_xboole_0(A_77,k4_xboole_0(B_78,A_77)) = k2_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_456,plain,(
    ! [B_4] : k2_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_441])).

tff(c_849,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_456])).

tff(c_830,plain,(
    ! [B_4] : k5_xboole_0(k5_xboole_0(B_4,B_4),B_4) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_797])).

tff(c_846,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k2_xboole_0(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_830])).

tff(c_968,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_846])).

tff(c_941,plain,(
    ! [B_4,C_113] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_113)) = k5_xboole_0(k1_xboole_0,C_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_890])).

tff(c_1283,plain,(
    ! [B_131,C_132] : k5_xboole_0(B_131,k5_xboole_0(B_131,C_132)) = C_132 ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_941])).

tff(c_1323,plain,(
    ! [B_112,A_111] : k5_xboole_0(B_112,k5_xboole_0(A_111,B_112)) = k5_xboole_0(A_111,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_1283])).

tff(c_1379,plain,(
    ! [B_133,A_134] : k5_xboole_0(B_133,k5_xboole_0(A_134,B_133)) = A_134 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1323])).

tff(c_3185,plain,(
    ! [B_171,A_172] : k5_xboole_0(k4_xboole_0(B_171,A_172),k2_xboole_0(A_172,B_171)) = A_172 ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_1379])).

tff(c_1282,plain,(
    ! [B_4,C_113] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_113)) = C_113 ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_941])).

tff(c_3209,plain,(
    ! [B_171,A_172] : k5_xboole_0(k4_xboole_0(B_171,A_172),A_172) = k2_xboole_0(A_172,B_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_3185,c_1282])).

tff(c_2044,plain,(
    ! [B_145,A_146] : k5_xboole_0(B_145,k4_xboole_0(B_145,A_146)) = k3_xboole_0(A_146,B_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_1283])).

tff(c_1370,plain,(
    ! [B_112,A_111] : k5_xboole_0(B_112,k5_xboole_0(A_111,B_112)) = A_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1323])).

tff(c_2854,plain,(
    ! [B_165,A_166] : k5_xboole_0(k4_xboole_0(B_165,A_166),k3_xboole_0(A_166,B_165)) = B_165 ),
    inference(superposition,[status(thm),theory(equality)],[c_2044,c_1370])).

tff(c_4295,plain,(
    ! [A_191,B_192] : k5_xboole_0(k3_xboole_0(A_191,B_192),B_192) = k4_xboole_0(B_192,A_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_2854,c_1370])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_948,plain,(
    ! [A_7,B_8,C_113] : k5_xboole_0(A_7,k5_xboole_0(k3_xboole_0(A_7,B_8),C_113)) = k5_xboole_0(k4_xboole_0(A_7,B_8),C_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_890])).

tff(c_4308,plain,(
    ! [A_191,B_192] : k5_xboole_0(k4_xboole_0(A_191,B_192),B_192) = k5_xboole_0(A_191,k4_xboole_0(B_192,A_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4295,c_948])).

tff(c_4392,plain,(
    ! [B_192,A_191] : k2_xboole_0(B_192,A_191) = k2_xboole_0(A_191,B_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3209,c_966,c_4308])).

tff(c_20,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4414,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4392,c_52])).

tff(c_4415,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4392,c_20,c_4414])).

tff(c_4525,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1125,c_4415])).

tff(c_4529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:28:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.80  
% 4.37/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.81  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.37/1.81  
% 4.37/1.81  %Foreground sorts:
% 4.37/1.81  
% 4.37/1.81  
% 4.37/1.81  %Background operators:
% 4.37/1.81  
% 4.37/1.81  
% 4.37/1.81  %Foreground operators:
% 4.37/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.37/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.37/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.37/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.37/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.37/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.37/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.37/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.37/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.37/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.37/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.37/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.37/1.81  
% 4.50/1.82  tff(f_84, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 4.50/1.82  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.50/1.82  tff(f_65, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.50/1.82  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.50/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.50/1.82  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.50/1.82  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.50/1.82  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.50/1.82  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.50/1.82  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.50/1.82  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.50/1.82  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.50/1.82  tff(c_54, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.50/1.82  tff(c_22, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.50/1.82  tff(c_38, plain, (![A_30, B_31]: (r1_tarski(k1_tarski(A_30), B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.50/1.82  tff(c_269, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k1_xboole_0 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.50/1.82  tff(c_283, plain, (![A_30, B_31]: (k4_xboole_0(k1_tarski(A_30), B_31)=k1_xboole_0 | ~r2_hidden(A_30, B_31))), inference(resolution, [status(thm)], [c_38, c_269])).
% 4.50/1.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.50/1.82  tff(c_367, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.50/1.82  tff(c_388, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_367])).
% 4.50/1.82  tff(c_26, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.50/1.82  tff(c_890, plain, (![A_111, B_112, C_113]: (k5_xboole_0(k5_xboole_0(A_111, B_112), C_113)=k5_xboole_0(A_111, k5_xboole_0(B_112, C_113)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.50/1.82  tff(c_931, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k5_xboole_0(B_19, k3_xboole_0(A_18, B_19)))=k2_xboole_0(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_26, c_890])).
% 4.50/1.82  tff(c_1076, plain, (![A_120, B_121]: (k5_xboole_0(A_120, k4_xboole_0(B_121, A_120))=k2_xboole_0(A_120, B_121))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_931])).
% 4.50/1.82  tff(c_1110, plain, (![B_31, A_30]: (k2_xboole_0(B_31, k1_tarski(A_30))=k5_xboole_0(B_31, k1_xboole_0) | ~r2_hidden(A_30, B_31))), inference(superposition, [status(thm), theory('equality')], [c_283, c_1076])).
% 4.50/1.82  tff(c_1125, plain, (![B_31, A_30]: (k2_xboole_0(B_31, k1_tarski(A_30))=B_31 | ~r2_hidden(A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1110])).
% 4.50/1.82  tff(c_966, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_931])).
% 4.50/1.82  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.50/1.82  tff(c_284, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_269])).
% 4.50/1.82  tff(c_139, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=A_50 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.50/1.82  tff(c_146, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_139])).
% 4.50/1.82  tff(c_382, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_146, c_367])).
% 4.50/1.82  tff(c_393, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_284, c_382])).
% 4.50/1.82  tff(c_911, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k5_xboole_0(B_112, k5_xboole_0(A_111, B_112)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_890, c_393])).
% 4.50/1.82  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.50/1.82  tff(c_157, plain, (![A_53]: (k3_xboole_0(k1_xboole_0, A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_139])).
% 4.50/1.82  tff(c_166, plain, (![A_53]: (k3_xboole_0(A_53, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_157, c_2])).
% 4.50/1.82  tff(c_797, plain, (![A_106, B_107]: (k5_xboole_0(k5_xboole_0(A_106, B_107), k3_xboole_0(A_106, B_107))=k2_xboole_0(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.50/1.82  tff(c_839, plain, (![A_14]: (k5_xboole_0(A_14, k3_xboole_0(A_14, k1_xboole_0))=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_797])).
% 4.50/1.82  tff(c_847, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_166, c_839])).
% 4.50/1.82  tff(c_441, plain, (![A_77, B_78]: (k2_xboole_0(A_77, k4_xboole_0(B_78, A_77))=k2_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.50/1.82  tff(c_456, plain, (![B_4]: (k2_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_284, c_441])).
% 4.50/1.82  tff(c_849, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_847, c_456])).
% 4.50/1.82  tff(c_830, plain, (![B_4]: (k5_xboole_0(k5_xboole_0(B_4, B_4), B_4)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_146, c_797])).
% 4.50/1.82  tff(c_846, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k2_xboole_0(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_830])).
% 4.50/1.82  tff(c_968, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_849, c_846])).
% 4.50/1.82  tff(c_941, plain, (![B_4, C_113]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_113))=k5_xboole_0(k1_xboole_0, C_113))), inference(superposition, [status(thm), theory('equality')], [c_393, c_890])).
% 4.50/1.82  tff(c_1283, plain, (![B_131, C_132]: (k5_xboole_0(B_131, k5_xboole_0(B_131, C_132))=C_132)), inference(demodulation, [status(thm), theory('equality')], [c_968, c_941])).
% 4.50/1.82  tff(c_1323, plain, (![B_112, A_111]: (k5_xboole_0(B_112, k5_xboole_0(A_111, B_112))=k5_xboole_0(A_111, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_911, c_1283])).
% 4.50/1.82  tff(c_1379, plain, (![B_133, A_134]: (k5_xboole_0(B_133, k5_xboole_0(A_134, B_133))=A_134)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1323])).
% 4.50/1.82  tff(c_3185, plain, (![B_171, A_172]: (k5_xboole_0(k4_xboole_0(B_171, A_172), k2_xboole_0(A_172, B_171))=A_172)), inference(superposition, [status(thm), theory('equality')], [c_966, c_1379])).
% 4.50/1.82  tff(c_1282, plain, (![B_4, C_113]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_113))=C_113)), inference(demodulation, [status(thm), theory('equality')], [c_968, c_941])).
% 4.50/1.82  tff(c_3209, plain, (![B_171, A_172]: (k5_xboole_0(k4_xboole_0(B_171, A_172), A_172)=k2_xboole_0(A_172, B_171))), inference(superposition, [status(thm), theory('equality')], [c_3185, c_1282])).
% 4.50/1.82  tff(c_2044, plain, (![B_145, A_146]: (k5_xboole_0(B_145, k4_xboole_0(B_145, A_146))=k3_xboole_0(A_146, B_145))), inference(superposition, [status(thm), theory('equality')], [c_388, c_1283])).
% 4.50/1.82  tff(c_1370, plain, (![B_112, A_111]: (k5_xboole_0(B_112, k5_xboole_0(A_111, B_112))=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1323])).
% 4.50/1.82  tff(c_2854, plain, (![B_165, A_166]: (k5_xboole_0(k4_xboole_0(B_165, A_166), k3_xboole_0(A_166, B_165))=B_165)), inference(superposition, [status(thm), theory('equality')], [c_2044, c_1370])).
% 4.50/1.82  tff(c_4295, plain, (![A_191, B_192]: (k5_xboole_0(k3_xboole_0(A_191, B_192), B_192)=k4_xboole_0(B_192, A_191))), inference(superposition, [status(thm), theory('equality')], [c_2854, c_1370])).
% 4.50/1.82  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.50/1.82  tff(c_948, plain, (![A_7, B_8, C_113]: (k5_xboole_0(A_7, k5_xboole_0(k3_xboole_0(A_7, B_8), C_113))=k5_xboole_0(k4_xboole_0(A_7, B_8), C_113))), inference(superposition, [status(thm), theory('equality')], [c_14, c_890])).
% 4.50/1.82  tff(c_4308, plain, (![A_191, B_192]: (k5_xboole_0(k4_xboole_0(A_191, B_192), B_192)=k5_xboole_0(A_191, k4_xboole_0(B_192, A_191)))), inference(superposition, [status(thm), theory('equality')], [c_4295, c_948])).
% 4.50/1.82  tff(c_4392, plain, (![B_192, A_191]: (k2_xboole_0(B_192, A_191)=k2_xboole_0(A_191, B_192))), inference(demodulation, [status(thm), theory('equality')], [c_3209, c_966, c_4308])).
% 4.50/1.82  tff(c_20, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.50/1.82  tff(c_52, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.50/1.82  tff(c_4414, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4392, c_52])).
% 4.50/1.82  tff(c_4415, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4392, c_20, c_4414])).
% 4.50/1.82  tff(c_4525, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1125, c_4415])).
% 4.50/1.82  tff(c_4529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_4525])).
% 4.50/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.82  
% 4.50/1.82  Inference rules
% 4.50/1.82  ----------------------
% 4.50/1.82  #Ref     : 0
% 4.50/1.82  #Sup     : 1078
% 4.50/1.82  #Fact    : 0
% 4.50/1.82  #Define  : 0
% 4.50/1.82  #Split   : 0
% 4.50/1.82  #Chain   : 0
% 4.50/1.82  #Close   : 0
% 4.50/1.82  
% 4.50/1.82  Ordering : KBO
% 4.50/1.82  
% 4.50/1.82  Simplification rules
% 4.50/1.82  ----------------------
% 4.50/1.82  #Subsume      : 88
% 4.50/1.82  #Demod        : 852
% 4.50/1.82  #Tautology    : 655
% 4.50/1.82  #SimpNegUnit  : 49
% 4.50/1.82  #BackRed      : 5
% 4.50/1.82  
% 4.50/1.82  #Partial instantiations: 0
% 4.50/1.82  #Strategies tried      : 1
% 4.50/1.82  
% 4.50/1.82  Timing (in seconds)
% 4.50/1.82  ----------------------
% 4.50/1.82  Preprocessing        : 0.31
% 4.50/1.82  Parsing              : 0.17
% 4.50/1.82  CNF conversion       : 0.02
% 4.50/1.82  Main loop            : 0.75
% 4.50/1.82  Inferencing          : 0.26
% 4.50/1.82  Reduction            : 0.31
% 4.50/1.83  Demodulation         : 0.25
% 4.50/1.83  BG Simplification    : 0.03
% 4.50/1.83  Subsumption          : 0.10
% 4.50/1.83  Abstraction          : 0.04
% 4.50/1.83  MUC search           : 0.00
% 4.50/1.83  Cooper               : 0.00
% 4.50/1.83  Total                : 1.09
% 4.50/1.83  Index Insertion      : 0.00
% 4.50/1.83  Index Deletion       : 0.00
% 4.50/1.83  Index Matching       : 0.00
% 4.50/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
