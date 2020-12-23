%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:32 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   65 (  85 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   51 (  74 expanded)
%              Number of equality atoms :   39 (  60 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_34,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_260,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_283,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k4_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_260])).

tff(c_286,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_283])).

tff(c_54,plain,(
    ! [B_55] : k4_xboole_0(k1_tarski(B_55),k1_tarski(B_55)) != k1_tarski(B_55) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_287,plain,(
    ! [B_55] : k1_tarski(B_55) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_54])).

tff(c_26,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_277,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_260])).

tff(c_32,plain,(
    ! [A_18,B_19,C_20] : k5_xboole_0(k5_xboole_0(A_18,B_19),C_20) = k5_xboole_0(A_18,k5_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_777,plain,(
    ! [A_109,B_110] : k5_xboole_0(k5_xboole_0(A_109,B_110),k3_xboole_0(A_109,B_110)) = k2_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_820,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k5_xboole_0(B_19,k3_xboole_0(A_18,B_19))) = k2_xboole_0(A_18,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_777])).

tff(c_1288,plain,(
    ! [A_131,B_132] : k5_xboole_0(A_131,k4_xboole_0(B_132,A_131)) = k2_xboole_0(A_131,B_132) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_820])).

tff(c_140,plain,(
    ! [B_62,A_63] : k5_xboole_0(B_62,A_63) = k5_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_63] : k5_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_30])).

tff(c_537,plain,(
    ! [A_102,B_103,C_104] : k5_xboole_0(k5_xboole_0(A_102,B_103),C_104) = k5_xboole_0(A_102,k5_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_612,plain,(
    ! [A_21,C_104] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_104)) = k5_xboole_0(k1_xboole_0,C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_537])).

tff(c_625,plain,(
    ! [A_21,C_104] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_104)) = C_104 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_612])).

tff(c_1435,plain,(
    ! [A_141,B_142] : k5_xboole_0(A_141,k2_xboole_0(A_141,B_142)) = k4_xboole_0(B_142,A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_1288,c_625])).

tff(c_1487,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k4_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1435])).

tff(c_1496,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1487])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1531,plain,(
    ! [D_147] :
      ( ~ r2_hidden(D_147,k1_tarski('#skF_4'))
      | ~ r2_hidden(D_147,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_8])).

tff(c_1534,plain,
    ( ~ r2_hidden('#skF_3'(k1_tarski('#skF_4')),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_1531])).

tff(c_1537,plain,(
    ~ r2_hidden('#skF_3'(k1_tarski('#skF_4')),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_1534])).

tff(c_1540,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_1537])).

tff(c_1544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_1540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:30:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 3.20/1.48  
% 3.20/1.48  %Foreground sorts:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Background operators:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Foreground operators:
% 3.20/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.20/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.20/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.20/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.20/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.20/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.48  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.20/1.48  
% 3.20/1.49  tff(f_57, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.20/1.49  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.20/1.49  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.20/1.49  tff(f_80, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.20/1.49  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.20/1.49  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.20/1.49  tff(f_84, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.20/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.20/1.49  tff(f_55, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.20/1.49  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.20/1.49  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.20/1.49  tff(f_39, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.20/1.49  tff(c_34, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.20/1.49  tff(c_24, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.20/1.49  tff(c_260, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.49  tff(c_283, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k4_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_24, c_260])).
% 3.20/1.49  tff(c_286, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_283])).
% 3.20/1.49  tff(c_54, plain, (![B_55]: (k4_xboole_0(k1_tarski(B_55), k1_tarski(B_55))!=k1_tarski(B_55))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.49  tff(c_287, plain, (![B_55]: (k1_tarski(B_55)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_54])).
% 3.20/1.49  tff(c_26, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.20/1.49  tff(c_30, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.20/1.49  tff(c_58, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.20/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.49  tff(c_277, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_260])).
% 3.20/1.49  tff(c_32, plain, (![A_18, B_19, C_20]: (k5_xboole_0(k5_xboole_0(A_18, B_19), C_20)=k5_xboole_0(A_18, k5_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.49  tff(c_777, plain, (![A_109, B_110]: (k5_xboole_0(k5_xboole_0(A_109, B_110), k3_xboole_0(A_109, B_110))=k2_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.49  tff(c_820, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k5_xboole_0(B_19, k3_xboole_0(A_18, B_19)))=k2_xboole_0(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_32, c_777])).
% 3.20/1.49  tff(c_1288, plain, (![A_131, B_132]: (k5_xboole_0(A_131, k4_xboole_0(B_132, A_131))=k2_xboole_0(A_131, B_132))), inference(demodulation, [status(thm), theory('equality')], [c_277, c_820])).
% 3.20/1.49  tff(c_140, plain, (![B_62, A_63]: (k5_xboole_0(B_62, A_63)=k5_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.20/1.49  tff(c_156, plain, (![A_63]: (k5_xboole_0(k1_xboole_0, A_63)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_140, c_30])).
% 3.20/1.49  tff(c_537, plain, (![A_102, B_103, C_104]: (k5_xboole_0(k5_xboole_0(A_102, B_103), C_104)=k5_xboole_0(A_102, k5_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.49  tff(c_612, plain, (![A_21, C_104]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_104))=k5_xboole_0(k1_xboole_0, C_104))), inference(superposition, [status(thm), theory('equality')], [c_34, c_537])).
% 3.20/1.49  tff(c_625, plain, (![A_21, C_104]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_104))=C_104)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_612])).
% 3.20/1.49  tff(c_1435, plain, (![A_141, B_142]: (k5_xboole_0(A_141, k2_xboole_0(A_141, B_142))=k4_xboole_0(B_142, A_141))), inference(superposition, [status(thm), theory('equality')], [c_1288, c_625])).
% 3.20/1.49  tff(c_1487, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k4_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1435])).
% 3.20/1.49  tff(c_1496, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1487])).
% 3.20/1.49  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.49  tff(c_1531, plain, (![D_147]: (~r2_hidden(D_147, k1_tarski('#skF_4')) | ~r2_hidden(D_147, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1496, c_8])).
% 3.20/1.49  tff(c_1534, plain, (~r2_hidden('#skF_3'(k1_tarski('#skF_4')), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_1531])).
% 3.20/1.49  tff(c_1537, plain, (~r2_hidden('#skF_3'(k1_tarski('#skF_4')), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_287, c_1534])).
% 3.20/1.49  tff(c_1540, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_1537])).
% 3.20/1.49  tff(c_1544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_287, c_1540])).
% 3.20/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  Inference rules
% 3.20/1.49  ----------------------
% 3.20/1.49  #Ref     : 0
% 3.20/1.49  #Sup     : 364
% 3.20/1.49  #Fact    : 0
% 3.20/1.49  #Define  : 0
% 3.20/1.49  #Split   : 0
% 3.20/1.49  #Chain   : 0
% 3.20/1.49  #Close   : 0
% 3.20/1.49  
% 3.20/1.49  Ordering : KBO
% 3.20/1.49  
% 3.20/1.49  Simplification rules
% 3.20/1.49  ----------------------
% 3.20/1.49  #Subsume      : 15
% 3.20/1.49  #Demod        : 155
% 3.20/1.49  #Tautology    : 218
% 3.20/1.49  #SimpNegUnit  : 5
% 3.20/1.49  #BackRed      : 2
% 3.20/1.49  
% 3.20/1.49  #Partial instantiations: 0
% 3.20/1.49  #Strategies tried      : 1
% 3.20/1.49  
% 3.20/1.49  Timing (in seconds)
% 3.20/1.49  ----------------------
% 3.20/1.50  Preprocessing        : 0.33
% 3.20/1.50  Parsing              : 0.17
% 3.20/1.50  CNF conversion       : 0.02
% 3.20/1.50  Main loop            : 0.41
% 3.20/1.50  Inferencing          : 0.14
% 3.20/1.50  Reduction            : 0.16
% 3.20/1.50  Demodulation         : 0.13
% 3.20/1.50  BG Simplification    : 0.02
% 3.20/1.50  Subsumption          : 0.06
% 3.20/1.50  Abstraction          : 0.03
% 3.20/1.50  MUC search           : 0.00
% 3.20/1.50  Cooper               : 0.00
% 3.20/1.50  Total                : 0.76
% 3.20/1.50  Index Insertion      : 0.00
% 3.20/1.50  Index Deletion       : 0.00
% 3.20/1.50  Index Matching       : 0.00
% 3.20/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
