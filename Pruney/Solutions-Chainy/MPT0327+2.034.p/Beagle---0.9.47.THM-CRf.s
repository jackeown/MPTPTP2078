%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:34 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 745 expanded)
%              Number of leaves         :   31 ( 265 expanded)
%              Depth                    :   17
%              Number of atoms          :   76 ( 975 expanded)
%              Number of equality atoms :   56 ( 649 expanded)
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

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_58,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_tarski(A_34),B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_238,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k1_xboole_0
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_248,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(k1_tarski(A_34),B_35) = k1_xboole_0
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_44,c_238])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_330,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_351,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_330])).

tff(c_880,plain,(
    ! [A_116,B_117,C_118] : k5_xboole_0(k5_xboole_0(A_116,B_117),C_118) = k5_xboole_0(A_116,k5_xboole_0(B_117,C_118)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k3_xboole_0(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_893,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k5_xboole_0(B_117,k3_xboole_0(A_116,B_117))) = k2_xboole_0(A_116,B_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_32])).

tff(c_1093,plain,(
    ! [A_126,B_127] : k5_xboole_0(A_126,k4_xboole_0(B_127,A_126)) = k2_xboole_0(A_126,B_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_893])).

tff(c_1127,plain,(
    ! [B_35,A_34] :
      ( k2_xboole_0(B_35,k1_tarski(A_34)) = k5_xboole_0(B_35,k1_xboole_0)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_1093])).

tff(c_1145,plain,(
    ! [B_35,A_34] :
      ( k2_xboole_0(B_35,k1_tarski(A_34)) = B_35
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1127])).

tff(c_952,plain,(
    ! [A_116,B_117] : k5_xboole_0(A_116,k4_xboole_0(B_117,A_116)) = k2_xboole_0(A_116,B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_893])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_249,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_238])).

tff(c_136,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_345,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_330])).

tff(c_356,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_345])).

tff(c_1561,plain,(
    ! [A_146,B_147] : k5_xboole_0(A_146,k5_xboole_0(B_147,k5_xboole_0(A_146,B_147))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_880])).

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_163,plain,(
    ! [A_65] : k3_xboole_0(k1_xboole_0,A_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_136])).

tff(c_172,plain,(
    ! [A_65] : k3_xboole_0(A_65,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2])).

tff(c_790,plain,(
    ! [A_111,B_112] : k5_xboole_0(k5_xboole_0(A_111,B_112),k3_xboole_0(A_111,B_112)) = k2_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_829,plain,(
    ! [A_16] : k5_xboole_0(A_16,k3_xboole_0(A_16,k1_xboole_0)) = k2_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_790])).

tff(c_837,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_172,c_829])).

tff(c_480,plain,(
    ! [A_88,B_89] : k2_xboole_0(A_88,k4_xboole_0(B_89,A_88)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_498,plain,(
    ! [B_4] : k2_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_480])).

tff(c_839,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_498])).

tff(c_820,plain,(
    ! [B_4] : k5_xboole_0(k5_xboole_0(B_4,B_4),B_4) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_790])).

tff(c_836,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k2_xboole_0(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_820])).

tff(c_958,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_836])).

tff(c_931,plain,(
    ! [B_4,C_118] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_118)) = k5_xboole_0(k1_xboole_0,C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_880])).

tff(c_1413,plain,(
    ! [B_4,C_118] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_118)) = C_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_931])).

tff(c_1569,plain,(
    ! [B_147,A_146] : k5_xboole_0(B_147,k5_xboole_0(A_146,B_147)) = k5_xboole_0(A_146,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_1413])).

tff(c_1664,plain,(
    ! [B_148,A_149] : k5_xboole_0(B_148,k5_xboole_0(A_149,B_148)) = A_149 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1569])).

tff(c_3108,plain,(
    ! [B_176,A_177] : k5_xboole_0(k4_xboole_0(B_176,A_177),k2_xboole_0(A_177,B_176)) = A_177 ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_1664])).

tff(c_3132,plain,(
    ! [B_176,A_177] : k5_xboole_0(k4_xboole_0(B_176,A_177),A_177) = k2_xboole_0(A_177,B_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_3108,c_1413])).

tff(c_4556,plain,(
    ! [A_204,B_205] : k5_xboole_0(k3_xboole_0(A_204,B_205),k4_xboole_0(B_205,A_204)) = B_205 ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_1664])).

tff(c_4578,plain,(
    ! [A_204,B_205] : k5_xboole_0(k3_xboole_0(A_204,B_205),B_205) = k4_xboole_0(B_205,A_204) ),
    inference(superposition,[status(thm),theory(equality)],[c_4556,c_1413])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5322,plain,(
    ! [A_216,B_217,C_218] : k5_xboole_0(A_216,k5_xboole_0(k3_xboole_0(A_216,B_217),C_218)) = k5_xboole_0(k4_xboole_0(A_216,B_217),C_218) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_880])).

tff(c_5375,plain,(
    ! [A_204,B_205] : k5_xboole_0(k4_xboole_0(A_204,B_205),B_205) = k5_xboole_0(A_204,k4_xboole_0(B_205,A_204)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4578,c_5322])).

tff(c_5481,plain,(
    ! [B_205,A_204] : k2_xboole_0(B_205,A_204) = k2_xboole_0(A_204,B_205) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3132,c_952,c_5375])).

tff(c_20,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_56,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5495,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5481,c_56])).

tff(c_5496,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5481,c_20,c_5495])).

tff(c_5660,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1145,c_5496])).

tff(c_5664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5660])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/2.10  
% 4.83/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/2.10  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.83/2.10  
% 4.83/2.10  %Foreground sorts:
% 4.83/2.10  
% 4.83/2.10  
% 4.83/2.10  %Background operators:
% 4.83/2.10  
% 4.83/2.10  
% 4.83/2.10  %Foreground operators:
% 4.83/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.83/2.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.83/2.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.83/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.83/2.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.83/2.10  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.83/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.83/2.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.83/2.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.83/2.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.83/2.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.83/2.10  tff('#skF_2', type, '#skF_2': $i).
% 4.83/2.10  tff('#skF_1', type, '#skF_1': $i).
% 4.83/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/2.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.83/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/2.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.83/2.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.83/2.10  
% 4.83/2.11  tff(f_90, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 4.83/2.11  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.83/2.11  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.83/2.11  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.83/2.11  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.83/2.11  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.83/2.11  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.83/2.11  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.83/2.11  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.83/2.11  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.83/2.11  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.83/2.11  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.83/2.11  tff(c_58, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.83/2.11  tff(c_24, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.83/2.11  tff(c_44, plain, (![A_34, B_35]: (r1_tarski(k1_tarski(A_34), B_35) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.83/2.11  tff(c_238, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k1_xboole_0 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.83/2.11  tff(c_248, plain, (![A_34, B_35]: (k4_xboole_0(k1_tarski(A_34), B_35)=k1_xboole_0 | ~r2_hidden(A_34, B_35))), inference(resolution, [status(thm)], [c_44, c_238])).
% 4.83/2.11  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.83/2.11  tff(c_330, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.83/2.11  tff(c_351, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_330])).
% 4.83/2.11  tff(c_880, plain, (![A_116, B_117, C_118]: (k5_xboole_0(k5_xboole_0(A_116, B_117), C_118)=k5_xboole_0(A_116, k5_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.83/2.11  tff(c_32, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k3_xboole_0(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.83/2.11  tff(c_893, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k5_xboole_0(B_117, k3_xboole_0(A_116, B_117)))=k2_xboole_0(A_116, B_117))), inference(superposition, [status(thm), theory('equality')], [c_880, c_32])).
% 4.83/2.11  tff(c_1093, plain, (![A_126, B_127]: (k5_xboole_0(A_126, k4_xboole_0(B_127, A_126))=k2_xboole_0(A_126, B_127))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_893])).
% 4.83/2.11  tff(c_1127, plain, (![B_35, A_34]: (k2_xboole_0(B_35, k1_tarski(A_34))=k5_xboole_0(B_35, k1_xboole_0) | ~r2_hidden(A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_248, c_1093])).
% 4.83/2.11  tff(c_1145, plain, (![B_35, A_34]: (k2_xboole_0(B_35, k1_tarski(A_34))=B_35 | ~r2_hidden(A_34, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1127])).
% 4.83/2.11  tff(c_952, plain, (![A_116, B_117]: (k5_xboole_0(A_116, k4_xboole_0(B_117, A_116))=k2_xboole_0(A_116, B_117))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_893])).
% 4.83/2.11  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.83/2.11  tff(c_249, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_238])).
% 4.83/2.11  tff(c_136, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.83/2.11  tff(c_147, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_136])).
% 4.83/2.11  tff(c_345, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_147, c_330])).
% 4.83/2.11  tff(c_356, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_249, c_345])).
% 4.83/2.11  tff(c_1561, plain, (![A_146, B_147]: (k5_xboole_0(A_146, k5_xboole_0(B_147, k5_xboole_0(A_146, B_147)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_356, c_880])).
% 4.83/2.11  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.83/2.11  tff(c_163, plain, (![A_65]: (k3_xboole_0(k1_xboole_0, A_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_136])).
% 4.83/2.11  tff(c_172, plain, (![A_65]: (k3_xboole_0(A_65, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_163, c_2])).
% 4.83/2.11  tff(c_790, plain, (![A_111, B_112]: (k5_xboole_0(k5_xboole_0(A_111, B_112), k3_xboole_0(A_111, B_112))=k2_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.83/2.11  tff(c_829, plain, (![A_16]: (k5_xboole_0(A_16, k3_xboole_0(A_16, k1_xboole_0))=k2_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_790])).
% 4.83/2.11  tff(c_837, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_172, c_829])).
% 4.83/2.11  tff(c_480, plain, (![A_88, B_89]: (k2_xboole_0(A_88, k4_xboole_0(B_89, A_88))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.83/2.11  tff(c_498, plain, (![B_4]: (k2_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_249, c_480])).
% 4.83/2.11  tff(c_839, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_837, c_498])).
% 4.83/2.11  tff(c_820, plain, (![B_4]: (k5_xboole_0(k5_xboole_0(B_4, B_4), B_4)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_147, c_790])).
% 4.83/2.11  tff(c_836, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k2_xboole_0(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_356, c_820])).
% 4.83/2.11  tff(c_958, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_839, c_836])).
% 4.83/2.11  tff(c_931, plain, (![B_4, C_118]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_118))=k5_xboole_0(k1_xboole_0, C_118))), inference(superposition, [status(thm), theory('equality')], [c_356, c_880])).
% 4.83/2.11  tff(c_1413, plain, (![B_4, C_118]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_118))=C_118)), inference(demodulation, [status(thm), theory('equality')], [c_958, c_931])).
% 4.83/2.11  tff(c_1569, plain, (![B_147, A_146]: (k5_xboole_0(B_147, k5_xboole_0(A_146, B_147))=k5_xboole_0(A_146, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_1413])).
% 4.83/2.11  tff(c_1664, plain, (![B_148, A_149]: (k5_xboole_0(B_148, k5_xboole_0(A_149, B_148))=A_149)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1569])).
% 4.83/2.11  tff(c_3108, plain, (![B_176, A_177]: (k5_xboole_0(k4_xboole_0(B_176, A_177), k2_xboole_0(A_177, B_176))=A_177)), inference(superposition, [status(thm), theory('equality')], [c_952, c_1664])).
% 4.83/2.11  tff(c_3132, plain, (![B_176, A_177]: (k5_xboole_0(k4_xboole_0(B_176, A_177), A_177)=k2_xboole_0(A_177, B_176))), inference(superposition, [status(thm), theory('equality')], [c_3108, c_1413])).
% 4.83/2.11  tff(c_4556, plain, (![A_204, B_205]: (k5_xboole_0(k3_xboole_0(A_204, B_205), k4_xboole_0(B_205, A_204))=B_205)), inference(superposition, [status(thm), theory('equality')], [c_351, c_1664])).
% 4.83/2.11  tff(c_4578, plain, (![A_204, B_205]: (k5_xboole_0(k3_xboole_0(A_204, B_205), B_205)=k4_xboole_0(B_205, A_204))), inference(superposition, [status(thm), theory('equality')], [c_4556, c_1413])).
% 4.83/2.11  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.83/2.11  tff(c_5322, plain, (![A_216, B_217, C_218]: (k5_xboole_0(A_216, k5_xboole_0(k3_xboole_0(A_216, B_217), C_218))=k5_xboole_0(k4_xboole_0(A_216, B_217), C_218))), inference(superposition, [status(thm), theory('equality')], [c_14, c_880])).
% 4.83/2.11  tff(c_5375, plain, (![A_204, B_205]: (k5_xboole_0(k4_xboole_0(A_204, B_205), B_205)=k5_xboole_0(A_204, k4_xboole_0(B_205, A_204)))), inference(superposition, [status(thm), theory('equality')], [c_4578, c_5322])).
% 4.83/2.11  tff(c_5481, plain, (![B_205, A_204]: (k2_xboole_0(B_205, A_204)=k2_xboole_0(A_204, B_205))), inference(demodulation, [status(thm), theory('equality')], [c_3132, c_952, c_5375])).
% 4.83/2.11  tff(c_20, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.83/2.11  tff(c_56, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.83/2.11  tff(c_5495, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5481, c_56])).
% 4.83/2.11  tff(c_5496, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5481, c_20, c_5495])).
% 4.83/2.11  tff(c_5660, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1145, c_5496])).
% 4.83/2.11  tff(c_5664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_5660])).
% 4.83/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/2.11  
% 4.83/2.11  Inference rules
% 4.83/2.11  ----------------------
% 4.83/2.11  #Ref     : 0
% 4.83/2.11  #Sup     : 1365
% 4.83/2.11  #Fact    : 0
% 4.83/2.11  #Define  : 0
% 4.83/2.11  #Split   : 0
% 4.83/2.11  #Chain   : 0
% 4.83/2.11  #Close   : 0
% 4.83/2.11  
% 4.83/2.11  Ordering : KBO
% 4.83/2.11  
% 4.83/2.11  Simplification rules
% 4.83/2.11  ----------------------
% 4.83/2.11  #Subsume      : 106
% 4.83/2.11  #Demod        : 1087
% 4.83/2.11  #Tautology    : 867
% 4.83/2.11  #SimpNegUnit  : 50
% 4.83/2.11  #BackRed      : 5
% 4.83/2.11  
% 4.83/2.11  #Partial instantiations: 0
% 4.83/2.11  #Strategies tried      : 1
% 4.83/2.11  
% 4.83/2.11  Timing (in seconds)
% 4.83/2.11  ----------------------
% 5.08/2.12  Preprocessing        : 0.35
% 5.08/2.12  Parsing              : 0.18
% 5.08/2.12  CNF conversion       : 0.02
% 5.08/2.12  Main loop            : 0.91
% 5.08/2.12  Inferencing          : 0.30
% 5.08/2.12  Reduction            : 0.39
% 5.08/2.12  Demodulation         : 0.30
% 5.08/2.12  BG Simplification    : 0.04
% 5.08/2.12  Subsumption          : 0.13
% 5.08/2.12  Abstraction          : 0.05
% 5.08/2.12  MUC search           : 0.00
% 5.08/2.12  Cooper               : 0.00
% 5.08/2.12  Total                : 1.29
% 5.08/2.12  Index Insertion      : 0.00
% 5.08/2.12  Index Deletion       : 0.00
% 5.08/2.12  Index Matching       : 0.00
% 5.08/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
