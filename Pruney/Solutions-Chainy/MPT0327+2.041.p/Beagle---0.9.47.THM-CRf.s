%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:35 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   85 (1106 expanded)
%              Number of leaves         :   31 ( 387 expanded)
%              Depth                    :   17
%              Number of atoms          :   78 (1474 expanded)
%              Number of equality atoms :   58 ( 968 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_50,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_169,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_210,plain,(
    ! [A_61] : k3_xboole_0(k1_xboole_0,A_61) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_169])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_219,plain,(
    ! [A_61] : k3_xboole_0(A_61,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_2])).

tff(c_636,plain,(
    ! [A_95,B_96] : k5_xboole_0(k5_xboole_0(A_95,B_96),k3_xboole_0(A_95,B_96)) = k2_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_675,plain,(
    ! [A_14] : k5_xboole_0(A_14,k3_xboole_0(A_14,k1_xboole_0)) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_636])).

tff(c_683,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_219,c_675])).

tff(c_44,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_tarski(A_34),B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_141,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_912,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(k1_tarski(A_109),B_110) = k1_xboole_0
      | ~ r2_hidden(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_44,c_141])).

tff(c_20,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_928,plain,(
    ! [B_110,A_109] :
      ( k2_xboole_0(B_110,k1_tarski(A_109)) = k2_xboole_0(B_110,k1_xboole_0)
      | ~ r2_hidden(A_109,B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_20])).

tff(c_950,plain,(
    ! [B_110,A_109] :
      ( k2_xboole_0(B_110,k1_tarski(A_109)) = B_110
      | ~ r2_hidden(A_109,B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_928])).

tff(c_380,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_398,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_380])).

tff(c_724,plain,(
    ! [A_100,B_101,C_102] : k5_xboole_0(k5_xboole_0(A_100,B_101),C_102) = k5_xboole_0(A_100,k5_xboole_0(B_101,C_102)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k3_xboole_0(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_737,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k5_xboole_0(B_101,k3_xboole_0(A_100,B_101))) = k2_xboole_0(A_100,B_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_32])).

tff(c_796,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k4_xboole_0(B_101,A_100)) = k2_xboole_0(A_100,B_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_737])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_152,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_141])).

tff(c_424,plain,(
    ! [A_80,B_81] : k2_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_436,plain,(
    ! [B_4] : k2_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_424])).

tff(c_685,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_436])).

tff(c_180,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_169])).

tff(c_395,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_380])).

tff(c_406,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_395])).

tff(c_666,plain,(
    ! [B_4] : k5_xboole_0(k5_xboole_0(B_4,B_4),B_4) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_636])).

tff(c_682,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k2_xboole_0(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_666])).

tff(c_804,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_682])).

tff(c_775,plain,(
    ! [B_4,C_102] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_102)) = k5_xboole_0(k1_xboole_0,C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_724])).

tff(c_1127,plain,(
    ! [B_120,C_121] : k5_xboole_0(B_120,k5_xboole_0(B_120,C_121)) = C_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_775])).

tff(c_1770,plain,(
    ! [A_134,B_135] : k5_xboole_0(A_134,k2_xboole_0(A_134,B_135)) = k4_xboole_0(B_135,A_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_1127])).

tff(c_1198,plain,(
    ! [A_122,B_123] : k5_xboole_0(A_122,k5_xboole_0(B_123,k5_xboole_0(A_122,B_123))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_406])).

tff(c_1126,plain,(
    ! [B_4,C_102] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_102)) = C_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_775])).

tff(c_1206,plain,(
    ! [B_123,A_122] : k5_xboole_0(B_123,k5_xboole_0(A_122,B_123)) = k5_xboole_0(A_122,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1198,c_1126])).

tff(c_1283,plain,(
    ! [B_123,A_122] : k5_xboole_0(B_123,k5_xboole_0(A_122,B_123)) = A_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1206])).

tff(c_2524,plain,(
    ! [A_156,B_157] : k5_xboole_0(k2_xboole_0(A_156,B_157),k4_xboole_0(B_157,A_156)) = A_156 ),
    inference(superposition,[status(thm),theory(equality)],[c_1770,c_1283])).

tff(c_2536,plain,(
    ! [B_157,A_156] : k5_xboole_0(k4_xboole_0(B_157,A_156),A_156) = k2_xboole_0(A_156,B_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_2524,c_1283])).

tff(c_1836,plain,(
    ! [A_136,B_137] : k5_xboole_0(A_136,k4_xboole_0(A_136,B_137)) = k3_xboole_0(B_137,A_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_1127])).

tff(c_2770,plain,(
    ! [A_160,B_161] : k5_xboole_0(k4_xboole_0(A_160,B_161),k3_xboole_0(B_161,A_160)) = A_160 ),
    inference(superposition,[status(thm),theory(equality)],[c_1836,c_1283])).

tff(c_2791,plain,(
    ! [B_161,A_160] : k5_xboole_0(k3_xboole_0(B_161,A_160),A_160) = k4_xboole_0(A_160,B_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_2770,c_1283])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3520,plain,(
    ! [A_176,B_177,C_178] : k5_xboole_0(A_176,k5_xboole_0(k3_xboole_0(A_176,B_177),C_178)) = k5_xboole_0(k4_xboole_0(A_176,B_177),C_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_724])).

tff(c_3570,plain,(
    ! [B_161,A_160] : k5_xboole_0(k4_xboole_0(B_161,A_160),A_160) = k5_xboole_0(B_161,k4_xboole_0(A_160,B_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2791,c_3520])).

tff(c_3667,plain,(
    ! [B_161,A_160] : k2_xboole_0(B_161,A_160) = k2_xboole_0(A_160,B_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2536,c_796,c_3570])).

tff(c_48,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3679,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3667,c_48])).

tff(c_3680,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3667,c_20,c_3679])).

tff(c_3804,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_3680])).

tff(c_3808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:20:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.84  
% 4.50/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.84  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.50/1.84  
% 4.50/1.84  %Foreground sorts:
% 4.50/1.84  
% 4.50/1.84  
% 4.50/1.84  %Background operators:
% 4.50/1.84  
% 4.50/1.84  
% 4.50/1.84  %Foreground operators:
% 4.50/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.50/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.50/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.50/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.50/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.50/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.50/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.50/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.50/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.50/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.50/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.50/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.50/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.50/1.84  
% 4.50/1.86  tff(f_78, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 4.50/1.86  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.50/1.86  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.50/1.86  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.50/1.86  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.50/1.86  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.50/1.86  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.50/1.86  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.50/1.86  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.50/1.86  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.50/1.86  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.50/1.86  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.50/1.86  tff(c_50, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.50/1.86  tff(c_22, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.50/1.86  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.50/1.86  tff(c_169, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.50/1.86  tff(c_210, plain, (![A_61]: (k3_xboole_0(k1_xboole_0, A_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_169])).
% 4.50/1.86  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.50/1.86  tff(c_219, plain, (![A_61]: (k3_xboole_0(A_61, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_210, c_2])).
% 4.50/1.86  tff(c_636, plain, (![A_95, B_96]: (k5_xboole_0(k5_xboole_0(A_95, B_96), k3_xboole_0(A_95, B_96))=k2_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.50/1.86  tff(c_675, plain, (![A_14]: (k5_xboole_0(A_14, k3_xboole_0(A_14, k1_xboole_0))=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_636])).
% 4.50/1.86  tff(c_683, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_219, c_675])).
% 4.50/1.86  tff(c_44, plain, (![A_34, B_35]: (r1_tarski(k1_tarski(A_34), B_35) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.50/1.86  tff(c_141, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.50/1.86  tff(c_912, plain, (![A_109, B_110]: (k4_xboole_0(k1_tarski(A_109), B_110)=k1_xboole_0 | ~r2_hidden(A_109, B_110))), inference(resolution, [status(thm)], [c_44, c_141])).
% 4.50/1.86  tff(c_20, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.50/1.86  tff(c_928, plain, (![B_110, A_109]: (k2_xboole_0(B_110, k1_tarski(A_109))=k2_xboole_0(B_110, k1_xboole_0) | ~r2_hidden(A_109, B_110))), inference(superposition, [status(thm), theory('equality')], [c_912, c_20])).
% 4.50/1.86  tff(c_950, plain, (![B_110, A_109]: (k2_xboole_0(B_110, k1_tarski(A_109))=B_110 | ~r2_hidden(A_109, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_928])).
% 4.50/1.86  tff(c_380, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.50/1.86  tff(c_398, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_380])).
% 4.50/1.86  tff(c_724, plain, (![A_100, B_101, C_102]: (k5_xboole_0(k5_xboole_0(A_100, B_101), C_102)=k5_xboole_0(A_100, k5_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.50/1.86  tff(c_32, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k3_xboole_0(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.50/1.86  tff(c_737, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k5_xboole_0(B_101, k3_xboole_0(A_100, B_101)))=k2_xboole_0(A_100, B_101))), inference(superposition, [status(thm), theory('equality')], [c_724, c_32])).
% 4.50/1.86  tff(c_796, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k4_xboole_0(B_101, A_100))=k2_xboole_0(A_100, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_737])).
% 4.50/1.86  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.50/1.86  tff(c_152, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_141])).
% 4.50/1.86  tff(c_424, plain, (![A_80, B_81]: (k2_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.50/1.86  tff(c_436, plain, (![B_4]: (k2_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_152, c_424])).
% 4.50/1.86  tff(c_685, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_683, c_436])).
% 4.50/1.86  tff(c_180, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_169])).
% 4.50/1.86  tff(c_395, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_180, c_380])).
% 4.50/1.86  tff(c_406, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_395])).
% 4.50/1.86  tff(c_666, plain, (![B_4]: (k5_xboole_0(k5_xboole_0(B_4, B_4), B_4)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_180, c_636])).
% 4.50/1.86  tff(c_682, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k2_xboole_0(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_666])).
% 4.50/1.86  tff(c_804, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_685, c_682])).
% 4.50/1.86  tff(c_775, plain, (![B_4, C_102]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_102))=k5_xboole_0(k1_xboole_0, C_102))), inference(superposition, [status(thm), theory('equality')], [c_406, c_724])).
% 4.50/1.86  tff(c_1127, plain, (![B_120, C_121]: (k5_xboole_0(B_120, k5_xboole_0(B_120, C_121))=C_121)), inference(demodulation, [status(thm), theory('equality')], [c_804, c_775])).
% 4.50/1.86  tff(c_1770, plain, (![A_134, B_135]: (k5_xboole_0(A_134, k2_xboole_0(A_134, B_135))=k4_xboole_0(B_135, A_134))), inference(superposition, [status(thm), theory('equality')], [c_796, c_1127])).
% 4.50/1.86  tff(c_1198, plain, (![A_122, B_123]: (k5_xboole_0(A_122, k5_xboole_0(B_123, k5_xboole_0(A_122, B_123)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_724, c_406])).
% 4.50/1.86  tff(c_1126, plain, (![B_4, C_102]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_102))=C_102)), inference(demodulation, [status(thm), theory('equality')], [c_804, c_775])).
% 4.50/1.86  tff(c_1206, plain, (![B_123, A_122]: (k5_xboole_0(B_123, k5_xboole_0(A_122, B_123))=k5_xboole_0(A_122, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1198, c_1126])).
% 4.50/1.86  tff(c_1283, plain, (![B_123, A_122]: (k5_xboole_0(B_123, k5_xboole_0(A_122, B_123))=A_122)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1206])).
% 4.50/1.86  tff(c_2524, plain, (![A_156, B_157]: (k5_xboole_0(k2_xboole_0(A_156, B_157), k4_xboole_0(B_157, A_156))=A_156)), inference(superposition, [status(thm), theory('equality')], [c_1770, c_1283])).
% 4.50/1.86  tff(c_2536, plain, (![B_157, A_156]: (k5_xboole_0(k4_xboole_0(B_157, A_156), A_156)=k2_xboole_0(A_156, B_157))), inference(superposition, [status(thm), theory('equality')], [c_2524, c_1283])).
% 4.50/1.86  tff(c_1836, plain, (![A_136, B_137]: (k5_xboole_0(A_136, k4_xboole_0(A_136, B_137))=k3_xboole_0(B_137, A_136))), inference(superposition, [status(thm), theory('equality')], [c_398, c_1127])).
% 4.50/1.86  tff(c_2770, plain, (![A_160, B_161]: (k5_xboole_0(k4_xboole_0(A_160, B_161), k3_xboole_0(B_161, A_160))=A_160)), inference(superposition, [status(thm), theory('equality')], [c_1836, c_1283])).
% 4.50/1.86  tff(c_2791, plain, (![B_161, A_160]: (k5_xboole_0(k3_xboole_0(B_161, A_160), A_160)=k4_xboole_0(A_160, B_161))), inference(superposition, [status(thm), theory('equality')], [c_2770, c_1283])).
% 4.50/1.86  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.50/1.86  tff(c_3520, plain, (![A_176, B_177, C_178]: (k5_xboole_0(A_176, k5_xboole_0(k3_xboole_0(A_176, B_177), C_178))=k5_xboole_0(k4_xboole_0(A_176, B_177), C_178))), inference(superposition, [status(thm), theory('equality')], [c_14, c_724])).
% 4.50/1.86  tff(c_3570, plain, (![B_161, A_160]: (k5_xboole_0(k4_xboole_0(B_161, A_160), A_160)=k5_xboole_0(B_161, k4_xboole_0(A_160, B_161)))), inference(superposition, [status(thm), theory('equality')], [c_2791, c_3520])).
% 4.50/1.86  tff(c_3667, plain, (![B_161, A_160]: (k2_xboole_0(B_161, A_160)=k2_xboole_0(A_160, B_161))), inference(demodulation, [status(thm), theory('equality')], [c_2536, c_796, c_3570])).
% 4.50/1.86  tff(c_48, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.50/1.86  tff(c_3679, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3667, c_48])).
% 4.50/1.86  tff(c_3680, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3667, c_20, c_3679])).
% 4.50/1.86  tff(c_3804, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_950, c_3680])).
% 4.50/1.86  tff(c_3808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_3804])).
% 4.50/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.86  
% 4.50/1.86  Inference rules
% 4.50/1.86  ----------------------
% 4.50/1.86  #Ref     : 0
% 4.50/1.86  #Sup     : 915
% 4.50/1.86  #Fact    : 0
% 4.50/1.86  #Define  : 0
% 4.50/1.86  #Split   : 1
% 4.50/1.86  #Chain   : 0
% 4.50/1.86  #Close   : 0
% 4.50/1.86  
% 4.50/1.86  Ordering : KBO
% 4.50/1.86  
% 4.50/1.86  Simplification rules
% 4.50/1.86  ----------------------
% 4.50/1.86  #Subsume      : 43
% 4.50/1.86  #Demod        : 722
% 4.50/1.86  #Tautology    : 597
% 4.50/1.86  #SimpNegUnit  : 0
% 4.50/1.86  #BackRed      : 5
% 4.50/1.86  
% 4.50/1.86  #Partial instantiations: 0
% 4.50/1.86  #Strategies tried      : 1
% 4.50/1.86  
% 4.50/1.86  Timing (in seconds)
% 4.50/1.86  ----------------------
% 4.50/1.86  Preprocessing        : 0.32
% 4.50/1.86  Parsing              : 0.17
% 4.50/1.86  CNF conversion       : 0.02
% 4.50/1.86  Main loop            : 0.76
% 4.50/1.86  Inferencing          : 0.25
% 4.50/1.86  Reduction            : 0.31
% 4.50/1.87  Demodulation         : 0.25
% 4.50/1.87  BG Simplification    : 0.03
% 4.50/1.87  Subsumption          : 0.12
% 4.50/1.87  Abstraction          : 0.05
% 4.50/1.87  MUC search           : 0.00
% 4.50/1.87  Cooper               : 0.00
% 4.50/1.87  Total                : 1.13
% 4.50/1.87  Index Insertion      : 0.00
% 4.50/1.87  Index Deletion       : 0.00
% 4.50/1.87  Index Matching       : 0.00
% 4.50/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
