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
% DateTime   : Thu Dec  3 09:51:33 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   66 (  73 expanded)
%              Number of leaves         :   36 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  60 expanded)
%              Number of equality atoms :   37 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_24,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_270,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_293,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_270])).

tff(c_296,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_293])).

tff(c_44,plain,(
    ! [B_56] : k4_xboole_0(k1_tarski(B_56),k1_tarski(B_56)) != k1_tarski(B_56) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_297,plain,(
    ! [B_56] : k1_tarski(B_56) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_44])).

tff(c_14,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_290,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_270])).

tff(c_869,plain,(
    ! [A_115,B_116] : k5_xboole_0(k5_xboole_0(A_115,B_116),k3_xboole_0(A_115,B_116)) = k2_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] : k5_xboole_0(k5_xboole_0(A_19,B_20),C_21) = k5_xboole_0(A_19,k5_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_890,plain,(
    ! [A_115,B_116] : k5_xboole_0(A_115,k5_xboole_0(B_116,k3_xboole_0(A_115,B_116))) = k2_xboole_0(A_115,B_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_22])).

tff(c_1132,plain,(
    ! [A_130,B_131] : k5_xboole_0(A_130,k4_xboole_0(B_131,A_130)) = k2_xboole_0(A_130,B_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_890])).

tff(c_131,plain,(
    ! [B_65,A_66] : k5_xboole_0(B_65,A_66) = k5_xboole_0(A_66,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_147,plain,(
    ! [A_66] : k5_xboole_0(k1_xboole_0,A_66) = A_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_18])).

tff(c_530,plain,(
    ! [A_106,B_107,C_108] : k5_xboole_0(k5_xboole_0(A_106,B_107),C_108) = k5_xboole_0(A_106,k5_xboole_0(B_107,C_108)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_605,plain,(
    ! [A_22,C_108] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_108)) = k5_xboole_0(k1_xboole_0,C_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_530])).

tff(c_618,plain,(
    ! [A_22,C_108] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_108)) = C_108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_605])).

tff(c_1880,plain,(
    ! [A_159,B_160] : k5_xboole_0(A_159,k2_xboole_0(A_159,B_160)) = k4_xboole_0(B_160,A_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_618])).

tff(c_1935,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_xboole_0) = k4_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1880])).

tff(c_1944,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1935])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1960,plain,(
    r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1944,c_20])).

tff(c_8,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1984,plain,(
    ! [C_162] : ~ r2_hidden(C_162,k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1960,c_8])).

tff(c_1996,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_1984])).

tff(c_2002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_1996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:05:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.59  
% 3.62/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.59  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.62/1.59  
% 3.62/1.59  %Foreground sorts:
% 3.62/1.59  
% 3.62/1.59  
% 3.62/1.59  %Background operators:
% 3.62/1.59  
% 3.62/1.59  
% 3.62/1.59  %Foreground operators:
% 3.62/1.59  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.62/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.62/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.62/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.62/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.62/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.62/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.62/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.62/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.62/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.62/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.62/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.62/1.59  
% 3.62/1.61  tff(f_67, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.62/1.61  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.62/1.61  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.62/1.61  tff(f_90, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.62/1.61  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.62/1.61  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.62/1.61  tff(f_94, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.62/1.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.62/1.61  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.62/1.61  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.62/1.61  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.62/1.61  tff(f_63, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.62/1.61  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.62/1.61  tff(c_24, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.62/1.61  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.61  tff(c_270, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.62/1.61  tff(c_293, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_270])).
% 3.62/1.61  tff(c_296, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_293])).
% 3.62/1.61  tff(c_44, plain, (![B_56]: (k4_xboole_0(k1_tarski(B_56), k1_tarski(B_56))!=k1_tarski(B_56))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.62/1.61  tff(c_297, plain, (![B_56]: (k1_tarski(B_56)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_296, c_44])).
% 3.62/1.61  tff(c_14, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.62/1.61  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.62/1.61  tff(c_48, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.62/1.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.62/1.61  tff(c_290, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_270])).
% 3.62/1.61  tff(c_869, plain, (![A_115, B_116]: (k5_xboole_0(k5_xboole_0(A_115, B_116), k3_xboole_0(A_115, B_116))=k2_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.62/1.61  tff(c_22, plain, (![A_19, B_20, C_21]: (k5_xboole_0(k5_xboole_0(A_19, B_20), C_21)=k5_xboole_0(A_19, k5_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.62/1.61  tff(c_890, plain, (![A_115, B_116]: (k5_xboole_0(A_115, k5_xboole_0(B_116, k3_xboole_0(A_115, B_116)))=k2_xboole_0(A_115, B_116))), inference(superposition, [status(thm), theory('equality')], [c_869, c_22])).
% 3.62/1.61  tff(c_1132, plain, (![A_130, B_131]: (k5_xboole_0(A_130, k4_xboole_0(B_131, A_130))=k2_xboole_0(A_130, B_131))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_890])).
% 3.62/1.61  tff(c_131, plain, (![B_65, A_66]: (k5_xboole_0(B_65, A_66)=k5_xboole_0(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.62/1.61  tff(c_147, plain, (![A_66]: (k5_xboole_0(k1_xboole_0, A_66)=A_66)), inference(superposition, [status(thm), theory('equality')], [c_131, c_18])).
% 3.62/1.61  tff(c_530, plain, (![A_106, B_107, C_108]: (k5_xboole_0(k5_xboole_0(A_106, B_107), C_108)=k5_xboole_0(A_106, k5_xboole_0(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.62/1.61  tff(c_605, plain, (![A_22, C_108]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_108))=k5_xboole_0(k1_xboole_0, C_108))), inference(superposition, [status(thm), theory('equality')], [c_24, c_530])).
% 3.62/1.61  tff(c_618, plain, (![A_22, C_108]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_108))=C_108)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_605])).
% 3.62/1.61  tff(c_1880, plain, (![A_159, B_160]: (k5_xboole_0(A_159, k2_xboole_0(A_159, B_160))=k4_xboole_0(B_160, A_159))), inference(superposition, [status(thm), theory('equality')], [c_1132, c_618])).
% 3.62/1.61  tff(c_1935, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_xboole_0)=k4_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1880])).
% 3.62/1.61  tff(c_1944, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1935])).
% 3.62/1.61  tff(c_20, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.62/1.61  tff(c_1960, plain, (r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1944, c_20])).
% 3.62/1.61  tff(c_8, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.62/1.61  tff(c_1984, plain, (![C_162]: (~r2_hidden(C_162, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_1960, c_8])).
% 3.62/1.61  tff(c_1996, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_1984])).
% 3.62/1.61  tff(c_2002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_297, c_1996])).
% 3.62/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.61  
% 3.62/1.61  Inference rules
% 3.62/1.61  ----------------------
% 3.62/1.61  #Ref     : 0
% 3.62/1.61  #Sup     : 486
% 3.62/1.61  #Fact    : 0
% 3.62/1.61  #Define  : 0
% 3.62/1.61  #Split   : 0
% 3.62/1.61  #Chain   : 0
% 3.62/1.61  #Close   : 0
% 3.62/1.61  
% 3.62/1.61  Ordering : KBO
% 3.62/1.61  
% 3.62/1.61  Simplification rules
% 3.62/1.61  ----------------------
% 3.62/1.61  #Subsume      : 14
% 3.62/1.61  #Demod        : 237
% 3.62/1.61  #Tautology    : 269
% 3.62/1.61  #SimpNegUnit  : 4
% 3.62/1.61  #BackRed      : 2
% 3.62/1.61  
% 3.62/1.61  #Partial instantiations: 0
% 3.62/1.61  #Strategies tried      : 1
% 3.62/1.61  
% 3.62/1.61  Timing (in seconds)
% 3.62/1.61  ----------------------
% 3.62/1.61  Preprocessing        : 0.33
% 3.62/1.61  Parsing              : 0.17
% 3.62/1.61  CNF conversion       : 0.02
% 3.62/1.61  Main loop            : 0.51
% 3.62/1.61  Inferencing          : 0.18
% 3.62/1.61  Reduction            : 0.20
% 3.62/1.61  Demodulation         : 0.17
% 3.62/1.61  BG Simplification    : 0.03
% 3.62/1.61  Subsumption          : 0.07
% 3.62/1.61  Abstraction          : 0.03
% 3.62/1.61  MUC search           : 0.00
% 3.62/1.61  Cooper               : 0.00
% 3.62/1.61  Total                : 0.87
% 3.62/1.61  Index Insertion      : 0.00
% 3.62/1.61  Index Deletion       : 0.00
% 3.62/1.61  Index Matching       : 0.00
% 3.62/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
