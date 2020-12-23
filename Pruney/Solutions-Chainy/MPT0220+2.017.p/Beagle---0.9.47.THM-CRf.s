%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:06 EST 2020

% Result     : Theorem 11.33s
% Output     : CNFRefutation 11.51s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 321 expanded)
%              Number of leaves         :   30 ( 122 expanded)
%              Depth                    :   20
%              Number of atoms          :   59 ( 344 expanded)
%              Number of equality atoms :   51 ( 289 expanded)
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

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_176,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_188,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_176])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_132,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k2_xboole_0(A_58,B_59)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_132])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_149,plain,(
    ! [A_61,B_62] :
      ( k3_xboole_0(A_61,B_62) = A_61
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_157,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_149])).

tff(c_185,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_176])).

tff(c_194,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_185])).

tff(c_423,plain,(
    ! [A_80,B_81,C_82] : k5_xboole_0(k5_xboole_0(A_80,B_81),C_82) = k5_xboole_0(A_80,k5_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_595,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k5_xboole_0(B_94,k5_xboole_0(A_93,B_94))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_194])).

tff(c_660,plain,(
    ! [B_95] : k5_xboole_0(B_95,k5_xboole_0(B_95,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_595])).

tff(c_770,plain,(
    ! [A_102] : k5_xboole_0(A_102,k5_xboole_0(k1_xboole_0,A_102)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_660])).

tff(c_4511,plain,(
    ! [B_151] : k5_xboole_0(k3_xboole_0(B_151,k1_xboole_0),k4_xboole_0(k1_xboole_0,B_151)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_770])).

tff(c_882,plain,(
    ! [B_109,C_110] : k5_xboole_0(B_109,k5_xboole_0(B_109,C_110)) = k5_xboole_0(k1_xboole_0,C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_423])).

tff(c_979,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = k5_xboole_0(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_882])).

tff(c_4534,plain,(
    ! [B_151] : k5_xboole_0(k4_xboole_0(k1_xboole_0,B_151),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(B_151,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4511,c_979])).

tff(c_6892,plain,(
    ! [B_176] : k5_xboole_0(k4_xboole_0(k1_xboole_0,B_176),k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_176) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_4534])).

tff(c_466,plain,(
    ! [A_17,B_18,C_82] : k5_xboole_0(A_17,k5_xboole_0(k4_xboole_0(B_18,A_17),C_82)) = k5_xboole_0(k2_xboole_0(A_17,B_18),C_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_423])).

tff(c_6904,plain,(
    ! [B_176] : k5_xboole_0(k2_xboole_0(B_176,k1_xboole_0),k1_xboole_0) = k5_xboole_0(B_176,k4_xboole_0(k1_xboole_0,B_176)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6892,c_466])).

tff(c_7053,plain,(
    ! [B_177] : k5_xboole_0(B_177,k1_xboole_0) = B_177 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22,c_14,c_6904])).

tff(c_7135,plain,(
    ! [B_177] : k5_xboole_0(k1_xboole_0,B_177) = B_177 ),
    inference(superposition,[status(thm),theory(equality)],[c_7053,c_4])).

tff(c_38,plain,(
    ! [A_47,B_48] : r1_tarski(k1_tarski(A_47),k2_tarski(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_560,plain,(
    ! [A_89,B_90] : k3_xboole_0(k1_tarski(A_89),k2_tarski(A_89,B_90)) = k1_tarski(A_89) ),
    inference(resolution,[status(thm)],[c_38,c_149])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_569,plain,(
    ! [A_89,B_90] : k5_xboole_0(k1_tarski(A_89),k1_tarski(A_89)) = k4_xboole_0(k1_tarski(A_89),k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_12])).

tff(c_577,plain,(
    ! [A_89,B_90] : k4_xboole_0(k1_tarski(A_89),k2_tarski(A_89,B_90)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_569])).

tff(c_6999,plain,(
    ! [B_176] : k5_xboole_0(B_176,k1_xboole_0) = B_176 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22,c_14,c_6904])).

tff(c_1485,plain,(
    ! [A_125,B_126,C_127] : k5_xboole_0(k5_xboole_0(A_125,B_126),C_127) = k5_xboole_0(B_126,k5_xboole_0(A_125,C_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_423])).

tff(c_8987,plain,(
    ! [B_199,A_198,B_197] : k5_xboole_0(B_199,k5_xboole_0(A_198,B_197)) = k5_xboole_0(B_197,k5_xboole_0(A_198,B_199)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1485])).

tff(c_10644,plain,(
    ! [B_220,B_221] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_220,B_221)) = k5_xboole_0(B_221,B_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_6999,c_8987])).

tff(c_10860,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_10644])).

tff(c_12044,plain,(
    ! [B_237,A_238] : k5_xboole_0(k3_xboole_0(B_237,A_238),A_238) = k4_xboole_0(A_238,B_237) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7135,c_10860])).

tff(c_480,plain,(
    ! [A_7,B_8,C_82] : k5_xboole_0(A_7,k5_xboole_0(k3_xboole_0(A_7,B_8),C_82)) = k5_xboole_0(k4_xboole_0(A_7,B_8),C_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_423])).

tff(c_12106,plain,(
    ! [B_237,A_238] : k5_xboole_0(k4_xboole_0(B_237,A_238),A_238) = k5_xboole_0(B_237,k4_xboole_0(A_238,B_237)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12044,c_480])).

tff(c_14877,plain,(
    ! [B_264,A_265] : k5_xboole_0(k4_xboole_0(B_264,A_265),A_265) = k2_xboole_0(B_264,A_265) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12106])).

tff(c_15039,plain,(
    ! [A_89,B_90] : k2_xboole_0(k1_tarski(A_89),k2_tarski(A_89,B_90)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_14877])).

tff(c_15080,plain,(
    ! [A_89,B_90] : k2_xboole_0(k1_tarski(A_89),k2_tarski(A_89,B_90)) = k2_tarski(A_89,B_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7135,c_15039])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_25726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15080,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:35:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.33/5.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.33/5.01  
% 11.33/5.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.33/5.02  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 11.33/5.02  
% 11.33/5.02  %Foreground sorts:
% 11.33/5.02  
% 11.33/5.02  
% 11.33/5.02  %Background operators:
% 11.33/5.02  
% 11.33/5.02  
% 11.33/5.02  %Foreground operators:
% 11.33/5.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.33/5.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.33/5.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.33/5.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.33/5.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.33/5.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.33/5.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.33/5.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.33/5.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.33/5.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.33/5.02  tff('#skF_2', type, '#skF_2': $i).
% 11.33/5.02  tff('#skF_1', type, '#skF_1': $i).
% 11.33/5.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.33/5.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.33/5.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.33/5.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.33/5.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.33/5.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.33/5.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.33/5.02  
% 11.51/5.03  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 11.51/5.03  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 11.51/5.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.51/5.03  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.51/5.03  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.51/5.03  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 11.51/5.03  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.51/5.03  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.51/5.03  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.51/5.03  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 11.51/5.03  tff(f_68, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 11.51/5.03  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.51/5.03  tff(c_22, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.51/5.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.51/5.03  tff(c_176, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.51/5.03  tff(c_188, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_176])).
% 11.51/5.03  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.51/5.03  tff(c_132, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k2_xboole_0(A_58, B_59))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.51/5.03  tff(c_139, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_132])).
% 11.51/5.03  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.51/5.03  tff(c_149, plain, (![A_61, B_62]: (k3_xboole_0(A_61, B_62)=A_61 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.51/5.03  tff(c_157, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_149])).
% 11.51/5.03  tff(c_185, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_157, c_176])).
% 11.51/5.03  tff(c_194, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_139, c_185])).
% 11.51/5.03  tff(c_423, plain, (![A_80, B_81, C_82]: (k5_xboole_0(k5_xboole_0(A_80, B_81), C_82)=k5_xboole_0(A_80, k5_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.51/5.03  tff(c_595, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k5_xboole_0(B_94, k5_xboole_0(A_93, B_94)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_423, c_194])).
% 11.51/5.03  tff(c_660, plain, (![B_95]: (k5_xboole_0(B_95, k5_xboole_0(B_95, k1_xboole_0))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_194, c_595])).
% 11.51/5.03  tff(c_770, plain, (![A_102]: (k5_xboole_0(A_102, k5_xboole_0(k1_xboole_0, A_102))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_660])).
% 11.51/5.03  tff(c_4511, plain, (![B_151]: (k5_xboole_0(k3_xboole_0(B_151, k1_xboole_0), k4_xboole_0(k1_xboole_0, B_151))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_188, c_770])).
% 11.51/5.03  tff(c_882, plain, (![B_109, C_110]: (k5_xboole_0(B_109, k5_xboole_0(B_109, C_110))=k5_xboole_0(k1_xboole_0, C_110))), inference(superposition, [status(thm), theory('equality')], [c_194, c_423])).
% 11.51/5.03  tff(c_979, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=k5_xboole_0(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_882])).
% 11.51/5.03  tff(c_4534, plain, (![B_151]: (k5_xboole_0(k4_xboole_0(k1_xboole_0, B_151), k1_xboole_0)=k5_xboole_0(k1_xboole_0, k3_xboole_0(B_151, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_4511, c_979])).
% 11.51/5.03  tff(c_6892, plain, (![B_176]: (k5_xboole_0(k4_xboole_0(k1_xboole_0, B_176), k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_4534])).
% 11.51/5.03  tff(c_466, plain, (![A_17, B_18, C_82]: (k5_xboole_0(A_17, k5_xboole_0(k4_xboole_0(B_18, A_17), C_82))=k5_xboole_0(k2_xboole_0(A_17, B_18), C_82))), inference(superposition, [status(thm), theory('equality')], [c_22, c_423])).
% 11.51/5.03  tff(c_6904, plain, (![B_176]: (k5_xboole_0(k2_xboole_0(B_176, k1_xboole_0), k1_xboole_0)=k5_xboole_0(B_176, k4_xboole_0(k1_xboole_0, B_176)))), inference(superposition, [status(thm), theory('equality')], [c_6892, c_466])).
% 11.51/5.03  tff(c_7053, plain, (![B_177]: (k5_xboole_0(B_177, k1_xboole_0)=B_177)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22, c_14, c_6904])).
% 11.51/5.03  tff(c_7135, plain, (![B_177]: (k5_xboole_0(k1_xboole_0, B_177)=B_177)), inference(superposition, [status(thm), theory('equality')], [c_7053, c_4])).
% 11.51/5.03  tff(c_38, plain, (![A_47, B_48]: (r1_tarski(k1_tarski(A_47), k2_tarski(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.51/5.03  tff(c_560, plain, (![A_89, B_90]: (k3_xboole_0(k1_tarski(A_89), k2_tarski(A_89, B_90))=k1_tarski(A_89))), inference(resolution, [status(thm)], [c_38, c_149])).
% 11.51/5.03  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.51/5.03  tff(c_569, plain, (![A_89, B_90]: (k5_xboole_0(k1_tarski(A_89), k1_tarski(A_89))=k4_xboole_0(k1_tarski(A_89), k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_560, c_12])).
% 11.51/5.03  tff(c_577, plain, (![A_89, B_90]: (k4_xboole_0(k1_tarski(A_89), k2_tarski(A_89, B_90))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_569])).
% 11.51/5.03  tff(c_6999, plain, (![B_176]: (k5_xboole_0(B_176, k1_xboole_0)=B_176)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22, c_14, c_6904])).
% 11.51/5.03  tff(c_1485, plain, (![A_125, B_126, C_127]: (k5_xboole_0(k5_xboole_0(A_125, B_126), C_127)=k5_xboole_0(B_126, k5_xboole_0(A_125, C_127)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_423])).
% 11.51/5.03  tff(c_8987, plain, (![B_199, A_198, B_197]: (k5_xboole_0(B_199, k5_xboole_0(A_198, B_197))=k5_xboole_0(B_197, k5_xboole_0(A_198, B_199)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1485])).
% 11.51/5.03  tff(c_10644, plain, (![B_220, B_221]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_220, B_221))=k5_xboole_0(B_221, B_220))), inference(superposition, [status(thm), theory('equality')], [c_6999, c_8987])).
% 11.51/5.03  tff(c_10860, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_10644])).
% 11.51/5.03  tff(c_12044, plain, (![B_237, A_238]: (k5_xboole_0(k3_xboole_0(B_237, A_238), A_238)=k4_xboole_0(A_238, B_237))), inference(demodulation, [status(thm), theory('equality')], [c_7135, c_10860])).
% 11.51/5.03  tff(c_480, plain, (![A_7, B_8, C_82]: (k5_xboole_0(A_7, k5_xboole_0(k3_xboole_0(A_7, B_8), C_82))=k5_xboole_0(k4_xboole_0(A_7, B_8), C_82))), inference(superposition, [status(thm), theory('equality')], [c_12, c_423])).
% 11.51/5.03  tff(c_12106, plain, (![B_237, A_238]: (k5_xboole_0(k4_xboole_0(B_237, A_238), A_238)=k5_xboole_0(B_237, k4_xboole_0(A_238, B_237)))), inference(superposition, [status(thm), theory('equality')], [c_12044, c_480])).
% 11.51/5.03  tff(c_14877, plain, (![B_264, A_265]: (k5_xboole_0(k4_xboole_0(B_264, A_265), A_265)=k2_xboole_0(B_264, A_265))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12106])).
% 11.51/5.03  tff(c_15039, plain, (![A_89, B_90]: (k2_xboole_0(k1_tarski(A_89), k2_tarski(A_89, B_90))=k5_xboole_0(k1_xboole_0, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_577, c_14877])).
% 11.51/5.03  tff(c_15080, plain, (![A_89, B_90]: (k2_xboole_0(k1_tarski(A_89), k2_tarski(A_89, B_90))=k2_tarski(A_89, B_90))), inference(demodulation, [status(thm), theory('equality')], [c_7135, c_15039])).
% 11.51/5.03  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.51/5.03  tff(c_25726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15080, c_40])).
% 11.51/5.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.51/5.03  
% 11.51/5.03  Inference rules
% 11.51/5.03  ----------------------
% 11.51/5.03  #Ref     : 0
% 11.51/5.03  #Sup     : 6360
% 11.51/5.03  #Fact    : 0
% 11.51/5.03  #Define  : 0
% 11.51/5.03  #Split   : 0
% 11.51/5.03  #Chain   : 0
% 11.51/5.03  #Close   : 0
% 11.51/5.03  
% 11.51/5.03  Ordering : KBO
% 11.51/5.03  
% 11.51/5.03  Simplification rules
% 11.51/5.03  ----------------------
% 11.51/5.03  #Subsume      : 336
% 11.51/5.03  #Demod        : 7999
% 11.51/5.03  #Tautology    : 3228
% 11.51/5.03  #SimpNegUnit  : 0
% 11.51/5.03  #BackRed      : 48
% 11.51/5.03  
% 11.51/5.03  #Partial instantiations: 0
% 11.51/5.03  #Strategies tried      : 1
% 11.51/5.03  
% 11.51/5.03  Timing (in seconds)
% 11.51/5.03  ----------------------
% 11.51/5.03  Preprocessing        : 0.31
% 11.51/5.03  Parsing              : 0.17
% 11.51/5.03  CNF conversion       : 0.02
% 11.51/5.03  Main loop            : 3.97
% 11.51/5.03  Inferencing          : 0.70
% 11.51/5.03  Reduction            : 2.55
% 11.51/5.03  Demodulation         : 2.37
% 11.51/5.03  BG Simplification    : 0.12
% 11.51/5.03  Subsumption          : 0.43
% 11.51/5.03  Abstraction          : 0.17
% 11.51/5.03  MUC search           : 0.00
% 11.51/5.03  Cooper               : 0.00
% 11.51/5.03  Total                : 4.31
% 11.51/5.03  Index Insertion      : 0.00
% 11.51/5.03  Index Deletion       : 0.00
% 11.51/5.03  Index Matching       : 0.00
% 11.51/5.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
