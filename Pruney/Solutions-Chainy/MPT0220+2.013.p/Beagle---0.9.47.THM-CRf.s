%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:05 EST 2020

% Result     : Theorem 10.25s
% Output     : CNFRefutation 10.32s
% Verified   : 
% Statistics : Number of formulae       :   55 (  85 expanded)
%              Number of leaves         :   27 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  69 expanded)
%              Number of equality atoms :   34 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_94,plain,(
    ! [B_47,A_48] : k5_xboole_0(B_47,A_48) = k5_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_110,plain,(
    ! [A_48] : k5_xboole_0(k1_xboole_0,A_48) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_20])).

tff(c_24,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_535,plain,(
    ! [A_84,B_85,C_86] : k5_xboole_0(k5_xboole_0(A_84,B_85),C_86) = k5_xboole_0(A_84,k5_xboole_0(B_85,C_86)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1631,plain,(
    ! [B_124,A_125,B_126] : k5_xboole_0(B_124,k5_xboole_0(A_125,B_126)) = k5_xboole_0(A_125,k5_xboole_0(B_126,B_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_535])).

tff(c_1999,plain,(
    ! [A_127,B_128] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_127,B_128)) = k5_xboole_0(B_128,A_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_1631])).

tff(c_2113,plain,(
    ! [B_18,A_17] : k5_xboole_0(k4_xboole_0(B_18,A_17),A_17) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1999])).

tff(c_2159,plain,(
    ! [B_18,A_17] : k5_xboole_0(k4_xboole_0(B_18,A_17),A_17) = k2_xboole_0(A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2113])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_274,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_294,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_274])).

tff(c_2104,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_1999])).

tff(c_2156,plain,(
    ! [B_2,A_1] : k5_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k4_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2104])).

tff(c_16,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6870,plain,(
    ! [A_189,B_190,C_191] : k5_xboole_0(A_189,k5_xboole_0(k3_xboole_0(A_189,B_190),C_191)) = k5_xboole_0(k4_xboole_0(A_189,B_190),C_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_535])).

tff(c_7010,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),A_1) = k5_xboole_0(B_2,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2156,c_6870])).

tff(c_7139,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2159,c_24,c_7010])).

tff(c_38,plain,(
    ! [A_40,B_41] : r1_tarski(k1_tarski(A_40),k2_tarski(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_218,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_229,plain,(
    ! [A_40,B_41] : k4_xboole_0(k1_tarski(A_40),k2_tarski(A_40,B_41)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_218])).

tff(c_249,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k4_xboole_0(B_65,A_64)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_262,plain,(
    ! [A_40,B_41] : k2_xboole_0(k2_tarski(A_40,B_41),k1_tarski(A_40)) = k5_xboole_0(k2_tarski(A_40,B_41),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_249])).

tff(c_9432,plain,(
    ! [A_214,B_215] : k2_xboole_0(k2_tarski(A_214,B_215),k1_tarski(A_214)) = k2_tarski(A_214,B_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_262])).

tff(c_9468,plain,(
    ! [A_214,B_215] : k2_xboole_0(k1_tarski(A_214),k2_tarski(A_214,B_215)) = k2_tarski(A_214,B_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_7139,c_9432])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_19558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9468,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n011.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 18:33:12 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.25/4.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.25/4.45  
% 10.25/4.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.25/4.45  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 10.25/4.45  
% 10.25/4.45  %Foreground sorts:
% 10.25/4.45  
% 10.25/4.45  
% 10.25/4.45  %Background operators:
% 10.25/4.45  
% 10.25/4.45  
% 10.25/4.45  %Foreground operators:
% 10.25/4.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.25/4.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.25/4.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.25/4.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.25/4.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.25/4.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.25/4.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.25/4.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.25/4.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.25/4.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.25/4.45  tff('#skF_2', type, '#skF_2': $i).
% 10.25/4.45  tff('#skF_1', type, '#skF_1': $i).
% 10.25/4.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.25/4.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.25/4.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.25/4.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.25/4.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.25/4.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.25/4.45  
% 10.32/4.46  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 10.32/4.46  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 10.32/4.46  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.32/4.46  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 10.32/4.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.32/4.46  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.32/4.46  tff(f_65, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 10.32/4.46  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.32/4.46  tff(f_68, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 10.32/4.46  tff(c_94, plain, (![B_47, A_48]: (k5_xboole_0(B_47, A_48)=k5_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.32/4.46  tff(c_20, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.32/4.46  tff(c_110, plain, (![A_48]: (k5_xboole_0(k1_xboole_0, A_48)=A_48)), inference(superposition, [status(thm), theory('equality')], [c_94, c_20])).
% 10.32/4.46  tff(c_24, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.32/4.46  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.32/4.46  tff(c_535, plain, (![A_84, B_85, C_86]: (k5_xboole_0(k5_xboole_0(A_84, B_85), C_86)=k5_xboole_0(A_84, k5_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.32/4.46  tff(c_1631, plain, (![B_124, A_125, B_126]: (k5_xboole_0(B_124, k5_xboole_0(A_125, B_126))=k5_xboole_0(A_125, k5_xboole_0(B_126, B_124)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_535])).
% 10.32/4.46  tff(c_1999, plain, (![A_127, B_128]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_127, B_128))=k5_xboole_0(B_128, A_127))), inference(superposition, [status(thm), theory('equality')], [c_110, c_1631])).
% 10.32/4.46  tff(c_2113, plain, (![B_18, A_17]: (k5_xboole_0(k4_xboole_0(B_18, A_17), A_17)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1999])).
% 10.32/4.46  tff(c_2159, plain, (![B_18, A_17]: (k5_xboole_0(k4_xboole_0(B_18, A_17), A_17)=k2_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2113])).
% 10.32/4.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.32/4.46  tff(c_274, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.32/4.46  tff(c_294, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_274])).
% 10.32/4.46  tff(c_2104, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_294, c_1999])).
% 10.32/4.46  tff(c_2156, plain, (![B_2, A_1]: (k5_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k4_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2104])).
% 10.32/4.46  tff(c_16, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.32/4.46  tff(c_6870, plain, (![A_189, B_190, C_191]: (k5_xboole_0(A_189, k5_xboole_0(k3_xboole_0(A_189, B_190), C_191))=k5_xboole_0(k4_xboole_0(A_189, B_190), C_191))), inference(superposition, [status(thm), theory('equality')], [c_16, c_535])).
% 10.32/4.46  tff(c_7010, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), A_1)=k5_xboole_0(B_2, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2156, c_6870])).
% 10.32/4.46  tff(c_7139, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_2159, c_24, c_7010])).
% 10.32/4.46  tff(c_38, plain, (![A_40, B_41]: (r1_tarski(k1_tarski(A_40), k2_tarski(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.32/4.46  tff(c_218, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.32/4.46  tff(c_229, plain, (![A_40, B_41]: (k4_xboole_0(k1_tarski(A_40), k2_tarski(A_40, B_41))=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_218])).
% 10.32/4.46  tff(c_249, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k4_xboole_0(B_65, A_64))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.32/4.46  tff(c_262, plain, (![A_40, B_41]: (k2_xboole_0(k2_tarski(A_40, B_41), k1_tarski(A_40))=k5_xboole_0(k2_tarski(A_40, B_41), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_229, c_249])).
% 10.32/4.46  tff(c_9432, plain, (![A_214, B_215]: (k2_xboole_0(k2_tarski(A_214, B_215), k1_tarski(A_214))=k2_tarski(A_214, B_215))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_262])).
% 10.32/4.46  tff(c_9468, plain, (![A_214, B_215]: (k2_xboole_0(k1_tarski(A_214), k2_tarski(A_214, B_215))=k2_tarski(A_214, B_215))), inference(superposition, [status(thm), theory('equality')], [c_7139, c_9432])).
% 10.32/4.46  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.32/4.46  tff(c_19558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9468, c_40])).
% 10.32/4.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.32/4.46  
% 10.32/4.46  Inference rules
% 10.32/4.46  ----------------------
% 10.32/4.46  #Ref     : 0
% 10.32/4.46  #Sup     : 4779
% 10.32/4.46  #Fact    : 0
% 10.32/4.46  #Define  : 0
% 10.32/4.46  #Split   : 0
% 10.32/4.46  #Chain   : 0
% 10.32/4.46  #Close   : 0
% 10.32/4.46  
% 10.32/4.46  Ordering : KBO
% 10.32/4.46  
% 10.32/4.46  Simplification rules
% 10.32/4.46  ----------------------
% 10.32/4.46  #Subsume      : 343
% 10.32/4.46  #Demod        : 5011
% 10.32/4.46  #Tautology    : 2254
% 10.32/4.46  #SimpNegUnit  : 0
% 10.32/4.46  #BackRed      : 1
% 10.32/4.46  
% 10.32/4.46  #Partial instantiations: 0
% 10.32/4.46  #Strategies tried      : 1
% 10.32/4.46  
% 10.32/4.46  Timing (in seconds)
% 10.32/4.46  ----------------------
% 10.32/4.47  Preprocessing        : 0.31
% 10.32/4.47  Parsing              : 0.16
% 10.32/4.47  CNF conversion       : 0.02
% 10.32/4.47  Main loop            : 3.42
% 10.32/4.47  Inferencing          : 0.63
% 10.32/4.47  Reduction            : 2.15
% 10.32/4.47  Demodulation         : 1.98
% 10.32/4.47  BG Simplification    : 0.09
% 10.32/4.47  Subsumption          : 0.41
% 10.32/4.47  Abstraction          : 0.14
% 10.32/4.47  MUC search           : 0.00
% 10.32/4.47  Cooper               : 0.00
% 10.32/4.47  Total                : 3.76
% 10.32/4.47  Index Insertion      : 0.00
% 10.32/4.47  Index Deletion       : 0.00
% 10.32/4.47  Index Matching       : 0.00
% 10.32/4.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
