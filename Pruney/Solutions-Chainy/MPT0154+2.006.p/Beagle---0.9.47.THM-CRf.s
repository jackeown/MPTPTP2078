%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:05 EST 2020

% Result     : Theorem 9.71s
% Output     : CNFRefutation 9.71s
% Verified   : 
% Statistics : Number of formulae       :   57 (  89 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   44 (  76 expanded)
%              Number of equality atoms :   43 (  75 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k1_tarski(A_18),k2_tarski(B_19,C_20)) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_253,plain,(
    ! [A_37,B_38] : k2_xboole_0(k1_tarski(A_37),k1_tarski(B_38)) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_199,plain,(
    ! [A_32,B_33] : k5_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_222,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_199])).

tff(c_225,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_222])).

tff(c_259,plain,(
    ! [A_37,B_38] : k4_xboole_0(k1_tarski(A_37),k2_tarski(A_37,B_38)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_225])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_219,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_199])).

tff(c_69,plain,(
    ! [B_27,A_28] : k5_xboole_0(B_27,A_28) = k5_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_28] : k5_xboole_0(k1_xboole_0,A_28) = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_317,plain,(
    ! [A_44,B_45,C_46] : k5_xboole_0(k5_xboole_0(A_44,B_45),C_46) = k5_xboole_0(A_44,k5_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_392,plain,(
    ! [A_13,C_46] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_46)) = k5_xboole_0(k1_xboole_0,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_317])).

tff(c_406,plain,(
    ! [A_47,C_48] : k5_xboole_0(A_47,k5_xboole_0(A_47,C_48)) = C_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_392])).

tff(c_442,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_406])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1903,plain,(
    ! [C_96,A_97,B_98] : k5_xboole_0(C_96,k5_xboole_0(A_97,B_98)) = k5_xboole_0(A_97,k5_xboole_0(B_98,C_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_4])).

tff(c_2847,plain,(
    ! [A_107,C_108] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_107,C_108)) = k5_xboole_0(C_108,A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_1903])).

tff(c_2935,plain,(
    ! [A_5,B_6] : k5_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k5_xboole_0(k1_xboole_0,k3_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_2847])).

tff(c_3011,plain,(
    ! [A_5,B_6] : k5_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k3_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2935])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7380,plain,(
    ! [A_163,B_164,C_165] : k5_xboole_0(A_163,k5_xboole_0(k4_xboole_0(B_164,A_163),C_165)) = k5_xboole_0(k2_xboole_0(A_163,B_164),C_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_317])).

tff(c_7481,plain,(
    ! [B_6,A_5] : k5_xboole_0(k2_xboole_0(B_6,A_5),A_5) = k5_xboole_0(B_6,k3_xboole_0(A_5,B_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3011,c_7380])).

tff(c_9090,plain,(
    ! [B_181,A_182] : k5_xboole_0(k2_xboole_0(B_181,A_182),A_182) = k4_xboole_0(B_181,A_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_7481])).

tff(c_405,plain,(
    ! [A_13,C_46] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_46)) = C_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_392])).

tff(c_19831,plain,(
    ! [B_235,A_236] : k5_xboole_0(k2_xboole_0(B_235,A_236),k4_xboole_0(B_235,A_236)) = A_236 ),
    inference(superposition,[status(thm),theory(equality)],[c_9090,c_405])).

tff(c_19989,plain,(
    ! [A_37,B_38] : k5_xboole_0(k2_xboole_0(k1_tarski(A_37),k2_tarski(A_37,B_38)),k1_xboole_0) = k2_tarski(A_37,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_19831])).

tff(c_20025,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20,c_19989])).

tff(c_24,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20025,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:09:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.71/4.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.71/4.36  
% 9.71/4.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.71/4.36  %$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 9.71/4.36  
% 9.71/4.36  %Foreground sorts:
% 9.71/4.36  
% 9.71/4.36  
% 9.71/4.36  %Background operators:
% 9.71/4.36  
% 9.71/4.36  
% 9.71/4.36  %Foreground operators:
% 9.71/4.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.71/4.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.71/4.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.71/4.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.71/4.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.71/4.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.71/4.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.71/4.36  tff('#skF_2', type, '#skF_2': $i).
% 9.71/4.36  tff('#skF_1', type, '#skF_1': $i).
% 9.71/4.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.71/4.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.71/4.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.71/4.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.71/4.36  
% 9.71/4.37  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 9.71/4.37  tff(f_45, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 9.71/4.37  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 9.71/4.37  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.71/4.37  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 9.71/4.37  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.71/4.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.71/4.37  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.71/4.37  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.71/4.37  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.71/4.37  tff(f_50, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.71/4.37  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.71/4.37  tff(c_20, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k1_tarski(A_18), k2_tarski(B_19, C_20))=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.71/4.37  tff(c_253, plain, (![A_37, B_38]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(B_38))=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.71/4.37  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.71/4.37  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.71/4.37  tff(c_199, plain, (![A_32, B_33]: (k5_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.71/4.37  tff(c_222, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k5_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_199])).
% 9.71/4.37  tff(c_225, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_222])).
% 9.71/4.37  tff(c_259, plain, (![A_37, B_38]: (k4_xboole_0(k1_tarski(A_37), k2_tarski(A_37, B_38))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_253, c_225])).
% 9.71/4.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.71/4.37  tff(c_219, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_199])).
% 9.71/4.37  tff(c_69, plain, (![B_27, A_28]: (k5_xboole_0(B_27, A_28)=k5_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.71/4.37  tff(c_85, plain, (![A_28]: (k5_xboole_0(k1_xboole_0, A_28)=A_28)), inference(superposition, [status(thm), theory('equality')], [c_69, c_10])).
% 9.71/4.37  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.71/4.37  tff(c_317, plain, (![A_44, B_45, C_46]: (k5_xboole_0(k5_xboole_0(A_44, B_45), C_46)=k5_xboole_0(A_44, k5_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.71/4.37  tff(c_392, plain, (![A_13, C_46]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_46))=k5_xboole_0(k1_xboole_0, C_46))), inference(superposition, [status(thm), theory('equality')], [c_14, c_317])).
% 9.71/4.37  tff(c_406, plain, (![A_47, C_48]: (k5_xboole_0(A_47, k5_xboole_0(A_47, C_48))=C_48)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_392])).
% 9.71/4.37  tff(c_442, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_406])).
% 9.71/4.37  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.71/4.37  tff(c_1903, plain, (![C_96, A_97, B_98]: (k5_xboole_0(C_96, k5_xboole_0(A_97, B_98))=k5_xboole_0(A_97, k5_xboole_0(B_98, C_96)))), inference(superposition, [status(thm), theory('equality')], [c_317, c_4])).
% 9.71/4.37  tff(c_2847, plain, (![A_107, C_108]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_107, C_108))=k5_xboole_0(C_108, A_107))), inference(superposition, [status(thm), theory('equality')], [c_85, c_1903])).
% 9.71/4.37  tff(c_2935, plain, (![A_5, B_6]: (k5_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k5_xboole_0(k1_xboole_0, k3_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_442, c_2847])).
% 9.71/4.37  tff(c_3011, plain, (![A_5, B_6]: (k5_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k3_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2935])).
% 9.71/4.37  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.71/4.37  tff(c_7380, plain, (![A_163, B_164, C_165]: (k5_xboole_0(A_163, k5_xboole_0(k4_xboole_0(B_164, A_163), C_165))=k5_xboole_0(k2_xboole_0(A_163, B_164), C_165))), inference(superposition, [status(thm), theory('equality')], [c_16, c_317])).
% 9.71/4.37  tff(c_7481, plain, (![B_6, A_5]: (k5_xboole_0(k2_xboole_0(B_6, A_5), A_5)=k5_xboole_0(B_6, k3_xboole_0(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_3011, c_7380])).
% 9.71/4.37  tff(c_9090, plain, (![B_181, A_182]: (k5_xboole_0(k2_xboole_0(B_181, A_182), A_182)=k4_xboole_0(B_181, A_182))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_7481])).
% 9.71/4.37  tff(c_405, plain, (![A_13, C_46]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_46))=C_46)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_392])).
% 9.71/4.37  tff(c_19831, plain, (![B_235, A_236]: (k5_xboole_0(k2_xboole_0(B_235, A_236), k4_xboole_0(B_235, A_236))=A_236)), inference(superposition, [status(thm), theory('equality')], [c_9090, c_405])).
% 9.71/4.37  tff(c_19989, plain, (![A_37, B_38]: (k5_xboole_0(k2_xboole_0(k1_tarski(A_37), k2_tarski(A_37, B_38)), k1_xboole_0)=k2_tarski(A_37, B_38))), inference(superposition, [status(thm), theory('equality')], [c_259, c_19831])).
% 9.71/4.37  tff(c_20025, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20, c_19989])).
% 9.71/4.37  tff(c_24, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.71/4.37  tff(c_20030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20025, c_24])).
% 9.71/4.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.71/4.37  
% 9.71/4.37  Inference rules
% 9.71/4.37  ----------------------
% 9.71/4.37  #Ref     : 0
% 9.71/4.37  #Sup     : 5090
% 9.71/4.37  #Fact    : 0
% 9.71/4.37  #Define  : 0
% 9.71/4.37  #Split   : 0
% 9.71/4.37  #Chain   : 0
% 9.71/4.37  #Close   : 0
% 9.71/4.37  
% 9.71/4.37  Ordering : KBO
% 9.71/4.37  
% 9.71/4.37  Simplification rules
% 9.71/4.37  ----------------------
% 9.71/4.37  #Subsume      : 249
% 9.71/4.37  #Demod        : 5242
% 9.71/4.37  #Tautology    : 2219
% 9.71/4.37  #SimpNegUnit  : 0
% 9.71/4.37  #BackRed      : 1
% 9.71/4.37  
% 9.71/4.37  #Partial instantiations: 0
% 9.71/4.37  #Strategies tried      : 1
% 9.71/4.37  
% 9.71/4.37  Timing (in seconds)
% 9.71/4.37  ----------------------
% 9.71/4.38  Preprocessing        : 0.29
% 9.71/4.38  Parsing              : 0.15
% 9.71/4.38  CNF conversion       : 0.02
% 9.71/4.38  Main loop            : 3.33
% 9.71/4.38  Inferencing          : 0.60
% 9.71/4.38  Reduction            : 2.11
% 9.71/4.38  Demodulation         : 1.96
% 9.71/4.38  BG Simplification    : 0.09
% 9.71/4.38  Subsumption          : 0.40
% 9.71/4.38  Abstraction          : 0.13
% 9.71/4.38  MUC search           : 0.00
% 9.71/4.38  Cooper               : 0.00
% 9.71/4.38  Total                : 3.65
% 9.71/4.38  Index Insertion      : 0.00
% 9.71/4.38  Index Deletion       : 0.00
% 9.71/4.38  Index Matching       : 0.00
% 9.71/4.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
