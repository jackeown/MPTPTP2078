%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:04 EST 2020

% Result     : Theorem 10.60s
% Output     : CNFRefutation 10.69s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 205 expanded)
%              Number of leaves         :   29 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 ( 237 expanded)
%              Number of equality atoms :   49 ( 172 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_141,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = k1_xboole_0
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_195,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k4_xboole_0(B_65,A_64)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_207,plain,(
    ! [B_8] : k5_xboole_0(B_8,k1_xboole_0) = k2_xboole_0(B_8,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_195])).

tff(c_231,plain,(
    ! [B_68] : k5_xboole_0(B_68,k1_xboole_0) = B_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_207])).

tff(c_251,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_231])).

tff(c_38,plain,(
    ! [A_41,B_42] : r1_tarski(k1_tarski(A_41),k2_tarski(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_148,plain,(
    ! [A_41,B_42] : k4_xboole_0(k1_tarski(A_41),k2_tarski(A_41,B_42)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_141])).

tff(c_204,plain,(
    ! [A_41,B_42] : k2_xboole_0(k2_tarski(A_41,B_42),k1_tarski(A_41)) = k5_xboole_0(k2_tarski(A_41,B_42),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_195])).

tff(c_210,plain,(
    ! [A_41,B_42] : k2_xboole_0(k2_tarski(A_41,B_42),k1_tarski(A_41)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_41,B_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_204])).

tff(c_15037,plain,(
    ! [A_238,B_239] : k2_xboole_0(k2_tarski(A_238,B_239),k1_tarski(A_238)) = k2_tarski(A_238,B_239) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_210])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_433,plain,(
    ! [A_80,B_81,C_82] : k5_xboole_0(k5_xboole_0(A_80,B_81),C_82) = k5_xboole_0(A_80,k5_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3005,plain,(
    ! [A_155,A_153,B_154] : k5_xboole_0(A_155,k5_xboole_0(A_153,B_154)) = k5_xboole_0(A_153,k5_xboole_0(B_154,A_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_433])).

tff(c_3541,plain,(
    ! [B_156,A_157] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_156,A_157)) = k5_xboole_0(A_157,B_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_3005])).

tff(c_3709,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3541])).

tff(c_3762,plain,(
    ! [B_19,A_18] : k5_xboole_0(k4_xboole_0(B_19,A_18),A_18) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_3709])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_911,plain,(
    ! [B_100,A_101] : k5_xboole_0(B_100,k3_xboole_0(A_101,B_100)) = k4_xboole_0(B_100,A_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_212])).

tff(c_157,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_165,plain,(
    ! [B_8] : k3_xboole_0(B_8,B_8) = B_8 ),
    inference(resolution,[status(thm)],[c_12,c_157])).

tff(c_221,plain,(
    ! [B_8] : k5_xboole_0(B_8,B_8) = k4_xboole_0(B_8,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_212])).

tff(c_230,plain,(
    ! [B_8] : k5_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_221])).

tff(c_473,plain,(
    ! [B_8,C_82] : k5_xboole_0(B_8,k5_xboole_0(B_8,C_82)) = k5_xboole_0(k1_xboole_0,C_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_433])).

tff(c_519,plain,(
    ! [B_8,C_82] : k5_xboole_0(B_8,k5_xboole_0(B_8,C_82)) = C_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_473])).

tff(c_1165,plain,(
    ! [B_115,A_116] : k5_xboole_0(B_115,k4_xboole_0(B_115,A_116)) = k3_xboole_0(A_116,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_911,c_519])).

tff(c_522,plain,(
    ! [B_83,C_84] : k5_xboole_0(B_83,k5_xboole_0(B_83,C_84)) = C_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_473])).

tff(c_574,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_522])).

tff(c_590,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k5_xboole_0(B_86,A_85)) = B_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_522])).

tff(c_617,plain,(
    ! [B_4,A_3] : k5_xboole_0(k5_xboole_0(B_4,A_3),B_4) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_590])).

tff(c_1177,plain,(
    ! [A_116,B_115] : k5_xboole_0(k3_xboole_0(A_116,B_115),B_115) = k4_xboole_0(B_115,A_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_617])).

tff(c_18,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6991,plain,(
    ! [A_190,B_191,C_192] : k5_xboole_0(A_190,k5_xboole_0(k3_xboole_0(A_190,B_191),C_192)) = k5_xboole_0(k4_xboole_0(A_190,B_191),C_192) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_433])).

tff(c_7124,plain,(
    ! [A_116,B_115] : k5_xboole_0(k4_xboole_0(A_116,B_115),B_115) = k5_xboole_0(A_116,k4_xboole_0(B_115,A_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1177,c_6991])).

tff(c_7256,plain,(
    ! [B_115,A_116] : k2_xboole_0(B_115,A_116) = k2_xboole_0(A_116,B_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3762,c_24,c_7124])).

tff(c_15052,plain,(
    ! [A_238,B_239] : k2_xboole_0(k1_tarski(A_238),k2_tarski(A_238,B_239)) = k2_tarski(A_238,B_239) ),
    inference(superposition,[status(thm),theory(equality)],[c_15037,c_7256])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15052,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.60/4.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.67/4.85  
% 10.67/4.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.67/4.85  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 10.67/4.85  
% 10.67/4.85  %Foreground sorts:
% 10.67/4.85  
% 10.67/4.85  
% 10.67/4.85  %Background operators:
% 10.67/4.85  
% 10.67/4.85  
% 10.67/4.85  %Foreground operators:
% 10.67/4.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.67/4.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.67/4.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.67/4.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.67/4.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.67/4.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.67/4.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.67/4.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.67/4.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.67/4.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.67/4.85  tff('#skF_2', type, '#skF_2': $i).
% 10.67/4.85  tff('#skF_1', type, '#skF_1': $i).
% 10.67/4.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.67/4.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.67/4.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.67/4.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.67/4.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.67/4.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.67/4.85  
% 10.69/4.86  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.69/4.86  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 10.69/4.86  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.69/4.86  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.69/4.86  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.69/4.86  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 10.69/4.86  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.69/4.86  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.69/4.86  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.69/4.86  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.69/4.86  tff(f_68, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 10.69/4.86  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.69/4.86  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.69/4.86  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.69/4.86  tff(c_141, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=k1_xboole_0 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.69/4.86  tff(c_149, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_141])).
% 10.69/4.86  tff(c_195, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k4_xboole_0(B_65, A_64))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.69/4.86  tff(c_207, plain, (![B_8]: (k5_xboole_0(B_8, k1_xboole_0)=k2_xboole_0(B_8, B_8))), inference(superposition, [status(thm), theory('equality')], [c_149, c_195])).
% 10.69/4.86  tff(c_231, plain, (![B_68]: (k5_xboole_0(B_68, k1_xboole_0)=B_68)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_207])).
% 10.69/4.86  tff(c_251, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_231])).
% 10.69/4.86  tff(c_38, plain, (![A_41, B_42]: (r1_tarski(k1_tarski(A_41), k2_tarski(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.69/4.86  tff(c_148, plain, (![A_41, B_42]: (k4_xboole_0(k1_tarski(A_41), k2_tarski(A_41, B_42))=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_141])).
% 10.69/4.86  tff(c_204, plain, (![A_41, B_42]: (k2_xboole_0(k2_tarski(A_41, B_42), k1_tarski(A_41))=k5_xboole_0(k2_tarski(A_41, B_42), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_148, c_195])).
% 10.69/4.86  tff(c_210, plain, (![A_41, B_42]: (k2_xboole_0(k2_tarski(A_41, B_42), k1_tarski(A_41))=k5_xboole_0(k1_xboole_0, k2_tarski(A_41, B_42)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_204])).
% 10.69/4.86  tff(c_15037, plain, (![A_238, B_239]: (k2_xboole_0(k2_tarski(A_238, B_239), k1_tarski(A_238))=k2_tarski(A_238, B_239))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_210])).
% 10.69/4.86  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.69/4.86  tff(c_433, plain, (![A_80, B_81, C_82]: (k5_xboole_0(k5_xboole_0(A_80, B_81), C_82)=k5_xboole_0(A_80, k5_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.69/4.86  tff(c_3005, plain, (![A_155, A_153, B_154]: (k5_xboole_0(A_155, k5_xboole_0(A_153, B_154))=k5_xboole_0(A_153, k5_xboole_0(B_154, A_155)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_433])).
% 10.69/4.86  tff(c_3541, plain, (![B_156, A_157]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_156, A_157))=k5_xboole_0(A_157, B_156))), inference(superposition, [status(thm), theory('equality')], [c_251, c_3005])).
% 10.69/4.86  tff(c_3709, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3541])).
% 10.69/4.86  tff(c_3762, plain, (![B_19, A_18]: (k5_xboole_0(k4_xboole_0(B_19, A_18), A_18)=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_3709])).
% 10.69/4.86  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.69/4.86  tff(c_212, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.69/4.86  tff(c_911, plain, (![B_100, A_101]: (k5_xboole_0(B_100, k3_xboole_0(A_101, B_100))=k4_xboole_0(B_100, A_101))), inference(superposition, [status(thm), theory('equality')], [c_2, c_212])).
% 10.69/4.86  tff(c_157, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.69/4.86  tff(c_165, plain, (![B_8]: (k3_xboole_0(B_8, B_8)=B_8)), inference(resolution, [status(thm)], [c_12, c_157])).
% 10.69/4.86  tff(c_221, plain, (![B_8]: (k5_xboole_0(B_8, B_8)=k4_xboole_0(B_8, B_8))), inference(superposition, [status(thm), theory('equality')], [c_165, c_212])).
% 10.69/4.86  tff(c_230, plain, (![B_8]: (k5_xboole_0(B_8, B_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_221])).
% 10.69/4.86  tff(c_473, plain, (![B_8, C_82]: (k5_xboole_0(B_8, k5_xboole_0(B_8, C_82))=k5_xboole_0(k1_xboole_0, C_82))), inference(superposition, [status(thm), theory('equality')], [c_230, c_433])).
% 10.69/4.86  tff(c_519, plain, (![B_8, C_82]: (k5_xboole_0(B_8, k5_xboole_0(B_8, C_82))=C_82)), inference(demodulation, [status(thm), theory('equality')], [c_251, c_473])).
% 10.69/4.86  tff(c_1165, plain, (![B_115, A_116]: (k5_xboole_0(B_115, k4_xboole_0(B_115, A_116))=k3_xboole_0(A_116, B_115))), inference(superposition, [status(thm), theory('equality')], [c_911, c_519])).
% 10.69/4.86  tff(c_522, plain, (![B_83, C_84]: (k5_xboole_0(B_83, k5_xboole_0(B_83, C_84))=C_84)), inference(demodulation, [status(thm), theory('equality')], [c_251, c_473])).
% 10.69/4.86  tff(c_574, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_522])).
% 10.69/4.86  tff(c_590, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k5_xboole_0(B_86, A_85))=B_86)), inference(superposition, [status(thm), theory('equality')], [c_4, c_522])).
% 10.69/4.86  tff(c_617, plain, (![B_4, A_3]: (k5_xboole_0(k5_xboole_0(B_4, A_3), B_4)=A_3)), inference(superposition, [status(thm), theory('equality')], [c_574, c_590])).
% 10.69/4.86  tff(c_1177, plain, (![A_116, B_115]: (k5_xboole_0(k3_xboole_0(A_116, B_115), B_115)=k4_xboole_0(B_115, A_116))), inference(superposition, [status(thm), theory('equality')], [c_1165, c_617])).
% 10.69/4.86  tff(c_18, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.69/4.86  tff(c_6991, plain, (![A_190, B_191, C_192]: (k5_xboole_0(A_190, k5_xboole_0(k3_xboole_0(A_190, B_191), C_192))=k5_xboole_0(k4_xboole_0(A_190, B_191), C_192))), inference(superposition, [status(thm), theory('equality')], [c_18, c_433])).
% 10.69/4.86  tff(c_7124, plain, (![A_116, B_115]: (k5_xboole_0(k4_xboole_0(A_116, B_115), B_115)=k5_xboole_0(A_116, k4_xboole_0(B_115, A_116)))), inference(superposition, [status(thm), theory('equality')], [c_1177, c_6991])).
% 10.69/4.86  tff(c_7256, plain, (![B_115, A_116]: (k2_xboole_0(B_115, A_116)=k2_xboole_0(A_116, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_3762, c_24, c_7124])).
% 10.69/4.86  tff(c_15052, plain, (![A_238, B_239]: (k2_xboole_0(k1_tarski(A_238), k2_tarski(A_238, B_239))=k2_tarski(A_238, B_239))), inference(superposition, [status(thm), theory('equality')], [c_15037, c_7256])).
% 10.69/4.86  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.69/4.86  tff(c_20968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15052, c_40])).
% 10.69/4.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.69/4.86  
% 10.69/4.86  Inference rules
% 10.69/4.86  ----------------------
% 10.69/4.86  #Ref     : 0
% 10.69/4.86  #Sup     : 5160
% 10.69/4.86  #Fact    : 0
% 10.69/4.86  #Define  : 0
% 10.69/4.86  #Split   : 0
% 10.69/4.86  #Chain   : 0
% 10.69/4.86  #Close   : 0
% 10.69/4.86  
% 10.69/4.87  Ordering : KBO
% 10.69/4.87  
% 10.69/4.87  Simplification rules
% 10.69/4.87  ----------------------
% 10.69/4.87  #Subsume      : 363
% 10.69/4.87  #Demod        : 5400
% 10.69/4.87  #Tautology    : 2272
% 10.69/4.87  #SimpNegUnit  : 0
% 10.69/4.87  #BackRed      : 1
% 10.69/4.87  
% 10.69/4.87  #Partial instantiations: 0
% 10.69/4.87  #Strategies tried      : 1
% 10.69/4.87  
% 10.69/4.87  Timing (in seconds)
% 10.69/4.87  ----------------------
% 10.69/4.87  Preprocessing        : 0.31
% 10.69/4.87  Parsing              : 0.16
% 10.69/4.87  CNF conversion       : 0.02
% 10.69/4.87  Main loop            : 3.78
% 10.69/4.87  Inferencing          : 0.65
% 10.69/4.87  Reduction            : 2.43
% 10.69/4.87  Demodulation         : 2.25
% 10.69/4.87  BG Simplification    : 0.10
% 10.69/4.87  Subsumption          : 0.45
% 10.69/4.87  Abstraction          : 0.15
% 10.69/4.87  MUC search           : 0.00
% 10.69/4.87  Cooper               : 0.00
% 10.69/4.87  Total                : 4.12
% 10.69/4.87  Index Insertion      : 0.00
% 10.69/4.87  Index Deletion       : 0.00
% 10.69/4.87  Index Matching       : 0.00
% 10.69/4.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
