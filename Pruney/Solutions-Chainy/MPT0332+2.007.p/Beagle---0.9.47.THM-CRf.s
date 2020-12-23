%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:49 EST 2020

% Result     : Theorem 10.62s
% Output     : CNFRefutation 10.73s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 113 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :   69 ( 120 expanded)
%              Number of equality atoms :   53 (  90 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(k2_xboole_0(C,k2_tarski(A,B)),k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k4_xboole_0(k5_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,k2_xboole_0(B,C)),k4_xboole_0(B,k2_xboole_0(A,C))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

tff(c_44,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ! [C_33,A_31,B_32] :
      ( k4_xboole_0(C_33,k2_tarski(A_31,B_32)) = C_33
      | r2_hidden(B_32,C_33)
      | r2_hidden(A_31,C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_143,plain,(
    ! [A_42,B_43] : k3_tarski(k2_tarski(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_197,plain,(
    ! [B_53,A_54] : k3_tarski(k2_tarski(B_53,A_54)) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_143])).

tff(c_36,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_203,plain,(
    ! [B_53,A_54] : k2_xboole_0(B_53,A_54) = k2_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_36])).

tff(c_28,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_495,plain,(
    ! [A_68,B_69] : k5_xboole_0(k5_xboole_0(A_68,B_69),k2_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_528,plain,(
    ! [A_17] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_17,A_17)) = k3_xboole_0(A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_495])).

tff(c_538,plain,(
    ! [A_17] : k5_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_528])).

tff(c_627,plain,(
    ! [A_73,B_74,C_75] : k5_xboole_0(k5_xboole_0(A_73,B_74),C_75) = k5_xboole_0(A_73,k5_xboole_0(B_74,C_75)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_684,plain,(
    ! [A_17,C_75] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_75)) = k5_xboole_0(k1_xboole_0,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_627])).

tff(c_841,plain,(
    ! [A_81,C_82] : k5_xboole_0(A_81,k5_xboole_0(A_81,C_82)) = C_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_684])).

tff(c_1704,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k2_xboole_0(A_100,B_101)) = k4_xboole_0(B_101,A_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_841])).

tff(c_1753,plain,(
    ! [A_54,B_53] : k5_xboole_0(A_54,k2_xboole_0(B_53,A_54)) = k4_xboole_0(B_53,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_1704])).

tff(c_220,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_36])).

tff(c_16,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_236,plain,(
    ! [A_56] : k2_xboole_0(k1_xboole_0,A_56) = A_56 ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_16])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_162,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_158])).

tff(c_328,plain,(
    ! [A_60,B_61,C_62] : k4_xboole_0(k4_xboole_0(A_60,B_61),C_62) = k4_xboole_0(A_60,k2_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_440,plain,(
    ! [B_66,C_67] : k4_xboole_0(B_66,k2_xboole_0(B_66,C_67)) = k4_xboole_0(k1_xboole_0,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_328])).

tff(c_486,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_440])).

tff(c_494,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_486])).

tff(c_350,plain,(
    ! [B_6,C_62] : k4_xboole_0(B_6,k2_xboole_0(B_6,C_62)) = k4_xboole_0(k1_xboole_0,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_328])).

tff(c_906,plain,(
    ! [B_83,C_84] : k4_xboole_0(B_83,k2_xboole_0(B_83,C_84)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_350])).

tff(c_945,plain,(
    ! [A_54,B_53] : k4_xboole_0(A_54,k2_xboole_0(B_53,A_54)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_906])).

tff(c_1127,plain,(
    ! [A_89,B_90,C_91] : k2_xboole_0(k4_xboole_0(A_89,k2_xboole_0(B_90,C_91)),k4_xboole_0(B_90,k2_xboole_0(A_89,C_91))) = k4_xboole_0(k5_xboole_0(A_89,B_90),C_91) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1242,plain,(
    ! [A_1,B_90] : k2_xboole_0(k4_xboole_0(A_1,k2_xboole_0(B_90,A_1)),k4_xboole_0(B_90,A_1)) = k4_xboole_0(k5_xboole_0(A_1,B_90),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1127])).

tff(c_7650,plain,(
    ! [A_203,B_204] : k4_xboole_0(k5_xboole_0(A_203,B_204),A_203) = k4_xboole_0(B_204,A_203) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_945,c_1242])).

tff(c_7811,plain,(
    ! [B_53,A_54] : k4_xboole_0(k4_xboole_0(B_53,A_54),A_54) = k4_xboole_0(k2_xboole_0(B_53,A_54),A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_1753,c_7650])).

tff(c_7897,plain,(
    ! [B_53,A_54] : k4_xboole_0(k2_xboole_0(B_53,A_54),A_54) = k4_xboole_0(B_53,A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18,c_7811])).

tff(c_40,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_21423,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7897,c_40])).

tff(c_21782,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_21423])).

tff(c_21786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_21782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:13:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.62/4.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.62/4.84  
% 10.62/4.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.62/4.84  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.62/4.84  
% 10.62/4.84  %Foreground sorts:
% 10.62/4.84  
% 10.62/4.84  
% 10.62/4.84  %Background operators:
% 10.62/4.84  
% 10.62/4.84  
% 10.62/4.84  %Foreground operators:
% 10.62/4.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.62/4.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.62/4.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.62/4.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.62/4.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.62/4.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.62/4.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.62/4.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.62/4.84  tff('#skF_2', type, '#skF_2': $i).
% 10.62/4.84  tff('#skF_3', type, '#skF_3': $i).
% 10.62/4.84  tff('#skF_1', type, '#skF_1': $i).
% 10.62/4.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.62/4.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.62/4.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.62/4.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.62/4.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.62/4.84  
% 10.73/4.85  tff(f_82, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(k2_xboole_0(C, k2_tarski(A, B)), k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 10.73/4.85  tff(f_71, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 10.73/4.85  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 10.73/4.85  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.73/4.85  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.73/4.85  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.73/4.85  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.73/4.85  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 10.73/4.85  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.73/4.85  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 10.73/4.85  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.73/4.85  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 10.73/4.85  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.73/4.85  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.73/4.85  tff(f_55, axiom, (![A, B, C]: (k4_xboole_0(k5_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, k2_xboole_0(B, C)), k4_xboole_0(B, k2_xboole_0(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_xboole_1)).
% 10.73/4.85  tff(c_44, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.73/4.85  tff(c_42, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.73/4.85  tff(c_38, plain, (![C_33, A_31, B_32]: (k4_xboole_0(C_33, k2_tarski(A_31, B_32))=C_33 | r2_hidden(B_32, C_33) | r2_hidden(A_31, C_33))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.73/4.85  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.73/4.85  tff(c_18, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.73/4.85  tff(c_32, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.73/4.85  tff(c_143, plain, (![A_42, B_43]: (k3_tarski(k2_tarski(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.73/4.85  tff(c_197, plain, (![B_53, A_54]: (k3_tarski(k2_tarski(B_53, A_54))=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_32, c_143])).
% 10.73/4.85  tff(c_36, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.73/4.85  tff(c_203, plain, (![B_53, A_54]: (k2_xboole_0(B_53, A_54)=k2_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_197, c_36])).
% 10.73/4.85  tff(c_28, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.73/4.85  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.73/4.85  tff(c_24, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.73/4.85  tff(c_495, plain, (![A_68, B_69]: (k5_xboole_0(k5_xboole_0(A_68, B_69), k2_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.73/4.85  tff(c_528, plain, (![A_17]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_17, A_17))=k3_xboole_0(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_24, c_495])).
% 10.73/4.85  tff(c_538, plain, (![A_17]: (k5_xboole_0(k1_xboole_0, A_17)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_528])).
% 10.73/4.85  tff(c_627, plain, (![A_73, B_74, C_75]: (k5_xboole_0(k5_xboole_0(A_73, B_74), C_75)=k5_xboole_0(A_73, k5_xboole_0(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.73/4.85  tff(c_684, plain, (![A_17, C_75]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_75))=k5_xboole_0(k1_xboole_0, C_75))), inference(superposition, [status(thm), theory('equality')], [c_24, c_627])).
% 10.73/4.85  tff(c_841, plain, (![A_81, C_82]: (k5_xboole_0(A_81, k5_xboole_0(A_81, C_82))=C_82)), inference(demodulation, [status(thm), theory('equality')], [c_538, c_684])).
% 10.73/4.85  tff(c_1704, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k2_xboole_0(A_100, B_101))=k4_xboole_0(B_101, A_100))), inference(superposition, [status(thm), theory('equality')], [c_28, c_841])).
% 10.73/4.85  tff(c_1753, plain, (![A_54, B_53]: (k5_xboole_0(A_54, k2_xboole_0(B_53, A_54))=k4_xboole_0(B_53, A_54))), inference(superposition, [status(thm), theory('equality')], [c_203, c_1704])).
% 10.73/4.85  tff(c_220, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_197, c_36])).
% 10.73/4.85  tff(c_16, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.73/4.85  tff(c_236, plain, (![A_56]: (k2_xboole_0(k1_xboole_0, A_56)=A_56)), inference(superposition, [status(thm), theory('equality')], [c_220, c_16])).
% 10.73/4.85  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.73/4.85  tff(c_158, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.73/4.85  tff(c_162, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_158])).
% 10.73/4.85  tff(c_328, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k4_xboole_0(A_60, B_61), C_62)=k4_xboole_0(A_60, k2_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.73/4.85  tff(c_440, plain, (![B_66, C_67]: (k4_xboole_0(B_66, k2_xboole_0(B_66, C_67))=k4_xboole_0(k1_xboole_0, C_67))), inference(superposition, [status(thm), theory('equality')], [c_162, c_328])).
% 10.73/4.85  tff(c_486, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_440])).
% 10.73/4.85  tff(c_494, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_486])).
% 10.73/4.85  tff(c_350, plain, (![B_6, C_62]: (k4_xboole_0(B_6, k2_xboole_0(B_6, C_62))=k4_xboole_0(k1_xboole_0, C_62))), inference(superposition, [status(thm), theory('equality')], [c_162, c_328])).
% 10.73/4.85  tff(c_906, plain, (![B_83, C_84]: (k4_xboole_0(B_83, k2_xboole_0(B_83, C_84))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_494, c_350])).
% 10.73/4.85  tff(c_945, plain, (![A_54, B_53]: (k4_xboole_0(A_54, k2_xboole_0(B_53, A_54))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_203, c_906])).
% 10.73/4.85  tff(c_1127, plain, (![A_89, B_90, C_91]: (k2_xboole_0(k4_xboole_0(A_89, k2_xboole_0(B_90, C_91)), k4_xboole_0(B_90, k2_xboole_0(A_89, C_91)))=k4_xboole_0(k5_xboole_0(A_89, B_90), C_91))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.73/4.85  tff(c_1242, plain, (![A_1, B_90]: (k2_xboole_0(k4_xboole_0(A_1, k2_xboole_0(B_90, A_1)), k4_xboole_0(B_90, A_1))=k4_xboole_0(k5_xboole_0(A_1, B_90), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1127])).
% 10.73/4.85  tff(c_7650, plain, (![A_203, B_204]: (k4_xboole_0(k5_xboole_0(A_203, B_204), A_203)=k4_xboole_0(B_204, A_203))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_945, c_1242])).
% 10.73/4.85  tff(c_7811, plain, (![B_53, A_54]: (k4_xboole_0(k4_xboole_0(B_53, A_54), A_54)=k4_xboole_0(k2_xboole_0(B_53, A_54), A_54))), inference(superposition, [status(thm), theory('equality')], [c_1753, c_7650])).
% 10.73/4.85  tff(c_7897, plain, (![B_53, A_54]: (k4_xboole_0(k2_xboole_0(B_53, A_54), A_54)=k4_xboole_0(B_53, A_54))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18, c_7811])).
% 10.73/4.85  tff(c_40, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.73/4.85  tff(c_21423, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7897, c_40])).
% 10.73/4.85  tff(c_21782, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_21423])).
% 10.73/4.85  tff(c_21786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_21782])).
% 10.73/4.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.73/4.85  
% 10.73/4.85  Inference rules
% 10.73/4.85  ----------------------
% 10.73/4.85  #Ref     : 0
% 10.73/4.85  #Sup     : 5502
% 10.73/4.85  #Fact    : 0
% 10.73/4.85  #Define  : 0
% 10.73/4.85  #Split   : 1
% 10.73/4.85  #Chain   : 0
% 10.73/4.85  #Close   : 0
% 10.73/4.85  
% 10.73/4.86  Ordering : KBO
% 10.73/4.86  
% 10.73/4.86  Simplification rules
% 10.73/4.86  ----------------------
% 10.73/4.86  #Subsume      : 67
% 10.73/4.86  #Demod        : 7069
% 10.73/4.86  #Tautology    : 2723
% 10.73/4.86  #SimpNegUnit  : 1
% 10.73/4.86  #BackRed      : 12
% 10.73/4.86  
% 10.73/4.86  #Partial instantiations: 0
% 10.73/4.86  #Strategies tried      : 1
% 10.73/4.86  
% 10.73/4.86  Timing (in seconds)
% 10.73/4.86  ----------------------
% 10.73/4.86  Preprocessing        : 0.33
% 10.73/4.86  Parsing              : 0.18
% 10.73/4.86  CNF conversion       : 0.02
% 10.73/4.86  Main loop            : 3.67
% 10.73/4.86  Inferencing          : 0.67
% 10.73/4.86  Reduction            : 2.29
% 10.73/4.86  Demodulation         : 2.10
% 10.73/4.86  BG Simplification    : 0.11
% 10.73/4.86  Subsumption          : 0.47
% 10.73/4.86  Abstraction          : 0.19
% 10.73/4.86  MUC search           : 0.00
% 10.73/4.86  Cooper               : 0.00
% 10.73/4.86  Total                : 4.03
% 10.73/4.86  Index Insertion      : 0.00
% 10.73/4.86  Index Deletion       : 0.00
% 10.73/4.86  Index Matching       : 0.00
% 10.73/4.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
