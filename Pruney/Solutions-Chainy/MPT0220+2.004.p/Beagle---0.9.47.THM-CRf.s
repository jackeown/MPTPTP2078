%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:04 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 173 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :   46 ( 181 expanded)
%              Number of equality atoms :   38 ( 141 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_30,plain,(
    ! [A_16] : k2_xboole_0(A_16,A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ! [B_19] : r1_tarski(B_19,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_164,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_176,plain,(
    ! [B_19] : k4_xboole_0(B_19,B_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_164])).

tff(c_242,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k4_xboole_0(B_85,A_84)) = k2_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_254,plain,(
    ! [B_19] : k5_xboole_0(B_19,k1_xboole_0) = k2_xboole_0(B_19,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_242])).

tff(c_259,plain,(
    ! [B_86] : k5_xboole_0(B_86,k1_xboole_0) = B_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_254])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_265,plain,(
    ! [B_86] : k5_xboole_0(k1_xboole_0,B_86) = B_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_4])).

tff(c_46,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_534,plain,(
    ! [A_103,B_104,C_105] : k5_xboole_0(k5_xboole_0(A_103,B_104),C_105) = k5_xboole_0(A_103,k5_xboole_0(B_104,C_105)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_973,plain,(
    ! [B_144,A_145,B_146] : k5_xboole_0(B_144,k5_xboole_0(A_145,B_146)) = k5_xboole_0(A_145,k5_xboole_0(B_146,B_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_534])).

tff(c_1232,plain,(
    ! [B_152,B_153] : k5_xboole_0(k1_xboole_0,k5_xboole_0(B_152,B_153)) = k5_xboole_0(B_153,B_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_973])).

tff(c_1297,plain,(
    ! [B_28,A_27] : k5_xboole_0(k4_xboole_0(B_28,A_27),A_27) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_27,B_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1232])).

tff(c_1321,plain,(
    ! [B_28,A_27] : k5_xboole_0(k4_xboole_0(B_28,A_27),A_27) = k2_xboole_0(A_27,B_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_1297])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_367,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k3_xboole_0(A_91,B_92)) = k4_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_387,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_367])).

tff(c_1282,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k5_xboole_0(k1_xboole_0,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_1232])).

tff(c_1317,plain,(
    ! [A_1,B_2] : k5_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k4_xboole_0(B_2,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_1282])).

tff(c_42,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3596,plain,(
    ! [A_217,B_218,C_219] : k5_xboole_0(A_217,k5_xboole_0(k3_xboole_0(A_217,B_218),C_219)) = k5_xboole_0(k4_xboole_0(A_217,B_218),C_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_534])).

tff(c_3718,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1317,c_3596])).

tff(c_3803,plain,(
    ! [B_220,A_221] : k2_xboole_0(B_220,A_221) = k2_xboole_0(A_221,B_220) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1321,c_46,c_3718])).

tff(c_60,plain,(
    ! [A_50,B_51] : r1_tarski(k1_tarski(A_50),k2_tarski(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_175,plain,(
    ! [A_50,B_51] : k4_xboole_0(k1_tarski(A_50),k2_tarski(A_50,B_51)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_164])).

tff(c_1549,plain,(
    ! [B_161,A_162] : k5_xboole_0(k4_xboole_0(B_161,A_162),A_162) = k2_xboole_0(A_162,B_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_1297])).

tff(c_1606,plain,(
    ! [A_50,B_51] : k2_xboole_0(k2_tarski(A_50,B_51),k1_tarski(A_50)) = k5_xboole_0(k1_xboole_0,k2_tarski(A_50,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_1549])).

tff(c_1629,plain,(
    ! [A_50,B_51] : k2_xboole_0(k2_tarski(A_50,B_51),k1_tarski(A_50)) = k2_tarski(A_50,B_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_1606])).

tff(c_3824,plain,(
    ! [A_50,B_51] : k2_xboole_0(k1_tarski(A_50),k2_tarski(A_50,B_51)) = k2_tarski(A_50,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_3803,c_1629])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_4','#skF_5')) != k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.37  
% 6.06/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.38  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.06/2.38  
% 6.06/2.38  %Foreground sorts:
% 6.06/2.38  
% 6.06/2.38  
% 6.06/2.38  %Background operators:
% 6.06/2.38  
% 6.06/2.38  
% 6.06/2.38  %Foreground operators:
% 6.06/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.06/2.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.06/2.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.06/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.06/2.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.06/2.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.06/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.06/2.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.06/2.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.06/2.38  tff('#skF_5', type, '#skF_5': $i).
% 6.06/2.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.06/2.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.06/2.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.06/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.38  tff('#skF_4', type, '#skF_4': $i).
% 6.06/2.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.06/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.06/2.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.06/2.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.06/2.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.06/2.38  
% 6.43/2.39  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.43/2.39  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.43/2.39  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.43/2.39  tff(f_64, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.43/2.39  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.43/2.39  tff(f_62, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.43/2.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.43/2.39  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.43/2.39  tff(f_78, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 6.43/2.39  tff(f_81, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 6.43/2.39  tff(c_30, plain, (![A_16]: (k2_xboole_0(A_16, A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.43/2.39  tff(c_36, plain, (![B_19]: (r1_tarski(B_19, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.43/2.39  tff(c_164, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.43/2.39  tff(c_176, plain, (![B_19]: (k4_xboole_0(B_19, B_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_164])).
% 6.43/2.39  tff(c_242, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k4_xboole_0(B_85, A_84))=k2_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.43/2.39  tff(c_254, plain, (![B_19]: (k5_xboole_0(B_19, k1_xboole_0)=k2_xboole_0(B_19, B_19))), inference(superposition, [status(thm), theory('equality')], [c_176, c_242])).
% 6.43/2.39  tff(c_259, plain, (![B_86]: (k5_xboole_0(B_86, k1_xboole_0)=B_86)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_254])).
% 6.43/2.39  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.43/2.39  tff(c_265, plain, (![B_86]: (k5_xboole_0(k1_xboole_0, B_86)=B_86)), inference(superposition, [status(thm), theory('equality')], [c_259, c_4])).
% 6.43/2.39  tff(c_46, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.43/2.39  tff(c_534, plain, (![A_103, B_104, C_105]: (k5_xboole_0(k5_xboole_0(A_103, B_104), C_105)=k5_xboole_0(A_103, k5_xboole_0(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.43/2.39  tff(c_973, plain, (![B_144, A_145, B_146]: (k5_xboole_0(B_144, k5_xboole_0(A_145, B_146))=k5_xboole_0(A_145, k5_xboole_0(B_146, B_144)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_534])).
% 6.43/2.39  tff(c_1232, plain, (![B_152, B_153]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(B_152, B_153))=k5_xboole_0(B_153, B_152))), inference(superposition, [status(thm), theory('equality')], [c_265, c_973])).
% 6.43/2.39  tff(c_1297, plain, (![B_28, A_27]: (k5_xboole_0(k4_xboole_0(B_28, A_27), A_27)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1232])).
% 6.43/2.39  tff(c_1321, plain, (![B_28, A_27]: (k5_xboole_0(k4_xboole_0(B_28, A_27), A_27)=k2_xboole_0(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_1297])).
% 6.43/2.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.43/2.39  tff(c_367, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k3_xboole_0(A_91, B_92))=k4_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.43/2.39  tff(c_387, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_367])).
% 6.43/2.39  tff(c_1282, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k5_xboole_0(k1_xboole_0, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_387, c_1232])).
% 6.43/2.39  tff(c_1317, plain, (![A_1, B_2]: (k5_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k4_xboole_0(B_2, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_1282])).
% 6.43/2.39  tff(c_42, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.43/2.39  tff(c_3596, plain, (![A_217, B_218, C_219]: (k5_xboole_0(A_217, k5_xboole_0(k3_xboole_0(A_217, B_218), C_219))=k5_xboole_0(k4_xboole_0(A_217, B_218), C_219))), inference(superposition, [status(thm), theory('equality')], [c_42, c_534])).
% 6.43/2.39  tff(c_3718, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_1317, c_3596])).
% 6.43/2.39  tff(c_3803, plain, (![B_220, A_221]: (k2_xboole_0(B_220, A_221)=k2_xboole_0(A_221, B_220))), inference(demodulation, [status(thm), theory('equality')], [c_1321, c_46, c_3718])).
% 6.43/2.39  tff(c_60, plain, (![A_50, B_51]: (r1_tarski(k1_tarski(A_50), k2_tarski(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.43/2.39  tff(c_175, plain, (![A_50, B_51]: (k4_xboole_0(k1_tarski(A_50), k2_tarski(A_50, B_51))=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_164])).
% 6.43/2.39  tff(c_1549, plain, (![B_161, A_162]: (k5_xboole_0(k4_xboole_0(B_161, A_162), A_162)=k2_xboole_0(A_162, B_161))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_1297])).
% 6.43/2.39  tff(c_1606, plain, (![A_50, B_51]: (k2_xboole_0(k2_tarski(A_50, B_51), k1_tarski(A_50))=k5_xboole_0(k1_xboole_0, k2_tarski(A_50, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_175, c_1549])).
% 6.43/2.39  tff(c_1629, plain, (![A_50, B_51]: (k2_xboole_0(k2_tarski(A_50, B_51), k1_tarski(A_50))=k2_tarski(A_50, B_51))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_1606])).
% 6.43/2.39  tff(c_3824, plain, (![A_50, B_51]: (k2_xboole_0(k1_tarski(A_50), k2_tarski(A_50, B_51))=k2_tarski(A_50, B_51))), inference(superposition, [status(thm), theory('equality')], [c_3803, c_1629])).
% 6.43/2.39  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_4', '#skF_5'))!=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.43/2.39  tff(c_4803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3824, c_62])).
% 6.43/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.43/2.39  
% 6.43/2.39  Inference rules
% 6.43/2.39  ----------------------
% 6.43/2.39  #Ref     : 1
% 6.43/2.39  #Sup     : 1191
% 6.43/2.39  #Fact    : 0
% 6.43/2.39  #Define  : 0
% 6.43/2.39  #Split   : 1
% 6.43/2.39  #Chain   : 0
% 6.43/2.39  #Close   : 0
% 6.43/2.39  
% 6.43/2.39  Ordering : KBO
% 6.43/2.39  
% 6.43/2.39  Simplification rules
% 6.43/2.39  ----------------------
% 6.43/2.39  #Subsume      : 174
% 6.43/2.39  #Demod        : 676
% 6.43/2.39  #Tautology    : 452
% 6.43/2.39  #SimpNegUnit  : 0
% 6.43/2.39  #BackRed      : 4
% 6.43/2.39  
% 6.43/2.39  #Partial instantiations: 0
% 6.43/2.39  #Strategies tried      : 1
% 6.43/2.39  
% 6.43/2.39  Timing (in seconds)
% 6.43/2.39  ----------------------
% 6.43/2.39  Preprocessing        : 0.41
% 6.43/2.39  Parsing              : 0.18
% 6.43/2.39  CNF conversion       : 0.03
% 6.43/2.39  Main loop            : 1.18
% 6.43/2.39  Inferencing          : 0.33
% 6.43/2.39  Reduction            : 0.58
% 6.43/2.39  Demodulation         : 0.50
% 6.43/2.39  BG Simplification    : 0.05
% 6.43/2.39  Subsumption          : 0.15
% 6.43/2.39  Abstraction          : 0.07
% 6.43/2.39  MUC search           : 0.00
% 6.43/2.39  Cooper               : 0.00
% 6.43/2.39  Total                : 1.63
% 6.43/2.39  Index Insertion      : 0.00
% 6.43/2.39  Index Deletion       : 0.00
% 6.43/2.39  Index Matching       : 0.00
% 6.43/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
