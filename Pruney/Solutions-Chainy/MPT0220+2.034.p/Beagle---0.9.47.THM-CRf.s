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
% DateTime   : Thu Dec  3 09:48:08 EST 2020

% Result     : Theorem 11.76s
% Output     : CNFRefutation 11.84s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 174 expanded)
%              Number of leaves         :   31 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :   60 ( 157 expanded)
%              Number of equality atoms :   55 ( 152 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_269,plain,(
    ! [A_79,B_80] : k2_xboole_0(k3_xboole_0(A_79,B_80),k4_xboole_0(A_79,B_80)) = A_79 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_275,plain,(
    ! [A_79,B_80] : k4_xboole_0(k3_xboole_0(A_79,B_80),A_79) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_18])).

tff(c_417,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_426,plain,(
    ! [A_79,B_80] : k2_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k5_xboole_0(A_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_417])).

tff(c_443,plain,(
    ! [A_87] : k5_xboole_0(A_87,k1_xboole_0) = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_426])).

tff(c_463,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_443])).

tff(c_24,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_538,plain,(
    ! [A_92,B_93,C_94] : k5_xboole_0(k5_xboole_0(A_92,B_93),C_94) = k5_xboole_0(A_92,k5_xboole_0(B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1581,plain,(
    ! [B_141,A_142,B_143] : k5_xboole_0(B_141,k5_xboole_0(A_142,B_143)) = k5_xboole_0(A_142,k5_xboole_0(B_143,B_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_538])).

tff(c_3095,plain,(
    ! [B_165,B_166] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_165,B_166)) = k5_xboole_0(B_166,B_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_1581])).

tff(c_3206,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3095])).

tff(c_3243,plain,(
    ! [B_21,A_20] : k5_xboole_0(k4_xboole_0(B_21,A_20),A_20) = k2_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_3206])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_254,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_263,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_254])).

tff(c_3188,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_3095])).

tff(c_3239,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_3188])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6722,plain,(
    ! [A_216,B_217,C_218] : k5_xboole_0(A_216,k5_xboole_0(k3_xboole_0(A_216,B_217),C_218)) = k5_xboole_0(k4_xboole_0(A_216,B_217),C_218) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_538])).

tff(c_6821,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3239,c_6722])).

tff(c_6957,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3243,c_24,c_6821])).

tff(c_156,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k2_xboole_0(A_64,B_65)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_773,plain,(
    ! [A_108] : k2_xboole_0(k3_xboole_0(A_108,A_108),k1_xboole_0) = A_108 ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_269])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_813,plain,(
    ! [A_115] : k3_xboole_0(A_115,A_115) = A_115 ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_12])).

tff(c_117,plain,(
    ! [B_62,A_63] : k3_xboole_0(B_62,A_63) = k3_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_132,plain,(
    ! [A_63,B_62] : k2_xboole_0(A_63,k3_xboole_0(B_62,A_63)) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_14])).

tff(c_839,plain,(
    ! [A_115] : k2_xboole_0(A_115,A_115) = A_115 ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_132])).

tff(c_40,plain,(
    ! [A_50,B_51] : r1_tarski(k1_tarski(A_50),k2_tarski(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_228,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = k1_xboole_0
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_237,plain,(
    ! [A_50,B_51] : k4_xboole_0(k1_tarski(A_50),k2_tarski(A_50,B_51)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_228])).

tff(c_429,plain,(
    ! [A_50,B_51] : k2_xboole_0(k2_tarski(A_50,B_51),k1_tarski(A_50)) = k5_xboole_0(k2_tarski(A_50,B_51),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_417])).

tff(c_442,plain,(
    ! [A_50,B_51] : k2_xboole_0(k2_tarski(A_50,B_51),k1_tarski(A_50)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_50,B_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_429])).

tff(c_17525,plain,(
    ! [A_308,B_309] : k2_xboole_0(k2_tarski(A_308,B_309),k1_tarski(A_308)) = k2_tarski(A_308,B_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_442])).

tff(c_1269,plain,(
    ! [A_133,B_134] : k2_xboole_0(k3_xboole_0(A_133,B_134),k4_xboole_0(B_134,A_133)) = B_134 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_269])).

tff(c_1313,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(k2_xboole_0(A_13,B_14),A_13),k1_xboole_0) = A_13 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1269])).

tff(c_1338,plain,(
    ! [A_135,B_136] : k3_xboole_0(A_135,k2_xboole_0(A_135,B_136)) = A_135 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2,c_1313])).

tff(c_1366,plain,(
    ! [A_135,B_136] : k2_xboole_0(k2_xboole_0(A_135,B_136),A_135) = k2_xboole_0(A_135,B_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_1338,c_132])).

tff(c_17618,plain,(
    ! [A_308,B_309] : k2_xboole_0(k2_tarski(A_308,B_309),k2_tarski(A_308,B_309)) = k2_xboole_0(k2_tarski(A_308,B_309),k1_tarski(A_308)) ),
    inference(superposition,[status(thm),theory(equality)],[c_17525,c_1366])).

tff(c_17658,plain,(
    ! [A_308,B_309] : k2_xboole_0(k1_tarski(A_308),k2_tarski(A_308,B_309)) = k2_tarski(A_308,B_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6957,c_839,c_17618])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_29001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17658,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:58:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.76/5.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.76/5.80  
% 11.76/5.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.76/5.80  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 11.76/5.80  
% 11.76/5.80  %Foreground sorts:
% 11.76/5.80  
% 11.76/5.80  
% 11.76/5.80  %Background operators:
% 11.76/5.80  
% 11.76/5.80  
% 11.76/5.80  %Foreground operators:
% 11.76/5.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.76/5.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.76/5.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.76/5.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.76/5.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.76/5.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.76/5.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.76/5.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.76/5.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.76/5.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.76/5.80  tff('#skF_2', type, '#skF_2': $i).
% 11.76/5.80  tff('#skF_1', type, '#skF_1': $i).
% 11.76/5.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.76/5.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.76/5.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.76/5.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.76/5.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.76/5.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.76/5.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.76/5.80  
% 11.84/5.82  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.84/5.82  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 11.84/5.82  tff(f_45, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 11.84/5.82  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 11.84/5.82  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.84/5.82  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.84/5.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.84/5.82  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.84/5.82  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 11.84/5.82  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 11.84/5.82  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.84/5.82  tff(f_68, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 11.84/5.82  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.84/5.82  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k3_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.84/5.82  tff(c_269, plain, (![A_79, B_80]: (k2_xboole_0(k3_xboole_0(A_79, B_80), k4_xboole_0(A_79, B_80))=A_79)), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.84/5.82  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.84/5.82  tff(c_275, plain, (![A_79, B_80]: (k4_xboole_0(k3_xboole_0(A_79, B_80), A_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_269, c_18])).
% 11.84/5.82  tff(c_417, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.84/5.82  tff(c_426, plain, (![A_79, B_80]: (k2_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k5_xboole_0(A_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_275, c_417])).
% 11.84/5.82  tff(c_443, plain, (![A_87]: (k5_xboole_0(A_87, k1_xboole_0)=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_426])).
% 11.84/5.82  tff(c_463, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_443])).
% 11.84/5.82  tff(c_24, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.84/5.82  tff(c_538, plain, (![A_92, B_93, C_94]: (k5_xboole_0(k5_xboole_0(A_92, B_93), C_94)=k5_xboole_0(A_92, k5_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.84/5.82  tff(c_1581, plain, (![B_141, A_142, B_143]: (k5_xboole_0(B_141, k5_xboole_0(A_142, B_143))=k5_xboole_0(A_142, k5_xboole_0(B_143, B_141)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_538])).
% 11.84/5.82  tff(c_3095, plain, (![B_165, B_166]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_165, B_166))=k5_xboole_0(B_166, B_165))), inference(superposition, [status(thm), theory('equality')], [c_463, c_1581])).
% 11.84/5.82  tff(c_3206, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3095])).
% 11.84/5.82  tff(c_3243, plain, (![B_21, A_20]: (k5_xboole_0(k4_xboole_0(B_21, A_20), A_20)=k2_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_3206])).
% 11.84/5.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.84/5.82  tff(c_254, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.84/5.82  tff(c_263, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_254])).
% 11.84/5.82  tff(c_3188, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_263, c_3095])).
% 11.84/5.82  tff(c_3239, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_3188])).
% 11.84/5.82  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.84/5.82  tff(c_6722, plain, (![A_216, B_217, C_218]: (k5_xboole_0(A_216, k5_xboole_0(k3_xboole_0(A_216, B_217), C_218))=k5_xboole_0(k4_xboole_0(A_216, B_217), C_218))), inference(superposition, [status(thm), theory('equality')], [c_10, c_538])).
% 11.84/5.82  tff(c_6821, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_3239, c_6722])).
% 11.84/5.82  tff(c_6957, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_3243, c_24, c_6821])).
% 11.84/5.82  tff(c_156, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k2_xboole_0(A_64, B_65))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.84/5.82  tff(c_163, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_156])).
% 11.84/5.82  tff(c_773, plain, (![A_108]: (k2_xboole_0(k3_xboole_0(A_108, A_108), k1_xboole_0)=A_108)), inference(superposition, [status(thm), theory('equality')], [c_163, c_269])).
% 11.84/5.82  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.84/5.82  tff(c_813, plain, (![A_115]: (k3_xboole_0(A_115, A_115)=A_115)), inference(superposition, [status(thm), theory('equality')], [c_773, c_12])).
% 11.84/5.82  tff(c_117, plain, (![B_62, A_63]: (k3_xboole_0(B_62, A_63)=k3_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.84/5.82  tff(c_132, plain, (![A_63, B_62]: (k2_xboole_0(A_63, k3_xboole_0(B_62, A_63))=A_63)), inference(superposition, [status(thm), theory('equality')], [c_117, c_14])).
% 11.84/5.82  tff(c_839, plain, (![A_115]: (k2_xboole_0(A_115, A_115)=A_115)), inference(superposition, [status(thm), theory('equality')], [c_813, c_132])).
% 11.84/5.82  tff(c_40, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), k2_tarski(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.84/5.82  tff(c_228, plain, (![A_71, B_72]: (k4_xboole_0(A_71, B_72)=k1_xboole_0 | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.84/5.82  tff(c_237, plain, (![A_50, B_51]: (k4_xboole_0(k1_tarski(A_50), k2_tarski(A_50, B_51))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_228])).
% 11.84/5.82  tff(c_429, plain, (![A_50, B_51]: (k2_xboole_0(k2_tarski(A_50, B_51), k1_tarski(A_50))=k5_xboole_0(k2_tarski(A_50, B_51), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_237, c_417])).
% 11.84/5.82  tff(c_442, plain, (![A_50, B_51]: (k2_xboole_0(k2_tarski(A_50, B_51), k1_tarski(A_50))=k5_xboole_0(k1_xboole_0, k2_tarski(A_50, B_51)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_429])).
% 11.84/5.82  tff(c_17525, plain, (![A_308, B_309]: (k2_xboole_0(k2_tarski(A_308, B_309), k1_tarski(A_308))=k2_tarski(A_308, B_309))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_442])).
% 11.84/5.82  tff(c_1269, plain, (![A_133, B_134]: (k2_xboole_0(k3_xboole_0(A_133, B_134), k4_xboole_0(B_134, A_133))=B_134)), inference(superposition, [status(thm), theory('equality')], [c_2, c_269])).
% 11.84/5.82  tff(c_1313, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(k2_xboole_0(A_13, B_14), A_13), k1_xboole_0)=A_13)), inference(superposition, [status(thm), theory('equality')], [c_18, c_1269])).
% 11.84/5.82  tff(c_1338, plain, (![A_135, B_136]: (k3_xboole_0(A_135, k2_xboole_0(A_135, B_136))=A_135)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2, c_1313])).
% 11.84/5.82  tff(c_1366, plain, (![A_135, B_136]: (k2_xboole_0(k2_xboole_0(A_135, B_136), A_135)=k2_xboole_0(A_135, B_136))), inference(superposition, [status(thm), theory('equality')], [c_1338, c_132])).
% 11.84/5.82  tff(c_17618, plain, (![A_308, B_309]: (k2_xboole_0(k2_tarski(A_308, B_309), k2_tarski(A_308, B_309))=k2_xboole_0(k2_tarski(A_308, B_309), k1_tarski(A_308)))), inference(superposition, [status(thm), theory('equality')], [c_17525, c_1366])).
% 11.84/5.82  tff(c_17658, plain, (![A_308, B_309]: (k2_xboole_0(k1_tarski(A_308), k2_tarski(A_308, B_309))=k2_tarski(A_308, B_309))), inference(demodulation, [status(thm), theory('equality')], [c_6957, c_839, c_17618])).
% 11.84/5.82  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.84/5.82  tff(c_29001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17658, c_42])).
% 11.84/5.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.84/5.82  
% 11.84/5.82  Inference rules
% 11.84/5.82  ----------------------
% 11.84/5.82  #Ref     : 0
% 11.84/5.82  #Sup     : 7276
% 11.84/5.82  #Fact    : 0
% 11.84/5.82  #Define  : 0
% 11.84/5.82  #Split   : 0
% 11.84/5.82  #Chain   : 0
% 11.84/5.82  #Close   : 0
% 11.84/5.82  
% 11.84/5.82  Ordering : KBO
% 11.84/5.82  
% 11.84/5.82  Simplification rules
% 11.84/5.82  ----------------------
% 11.84/5.82  #Subsume      : 369
% 11.84/5.82  #Demod        : 9551
% 11.84/5.82  #Tautology    : 4139
% 11.84/5.82  #SimpNegUnit  : 0
% 11.84/5.82  #BackRed      : 2
% 11.84/5.82  
% 11.84/5.82  #Partial instantiations: 0
% 11.84/5.82  #Strategies tried      : 1
% 11.84/5.82  
% 11.84/5.82  Timing (in seconds)
% 11.84/5.82  ----------------------
% 11.84/5.82  Preprocessing        : 0.32
% 11.84/5.82  Parsing              : 0.17
% 11.84/5.82  CNF conversion       : 0.02
% 11.84/5.82  Main loop            : 4.72
% 11.84/5.82  Inferencing          : 0.78
% 11.84/5.82  Reduction            : 3.05
% 11.84/5.82  Demodulation         : 2.84
% 11.84/5.82  BG Simplification    : 0.12
% 11.84/5.82  Subsumption          : 0.60
% 11.84/5.82  Abstraction          : 0.20
% 11.84/5.82  MUC search           : 0.00
% 11.84/5.82  Cooper               : 0.00
% 11.84/5.82  Total                : 5.07
% 11.84/5.82  Index Insertion      : 0.00
% 11.84/5.82  Index Deletion       : 0.00
% 11.84/5.82  Index Matching       : 0.00
% 11.84/5.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
