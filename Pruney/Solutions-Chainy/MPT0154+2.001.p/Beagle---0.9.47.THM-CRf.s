%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:04 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   53 (  75 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   31 (  53 expanded)
%              Number of equality atoms :   30 (  52 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_87,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_312,plain,(
    ! [A_71,B_72] : k2_xboole_0(k1_tarski(A_71),k1_tarski(B_72)) = k2_tarski(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_687,plain,(
    ! [B_99,A_100] : k2_xboole_0(k1_tarski(B_99),k1_tarski(A_100)) = k2_tarski(A_100,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_312])).

tff(c_72,plain,(
    ! [A_40,B_41] : k2_xboole_0(k1_tarski(A_40),k1_tarski(B_41)) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_693,plain,(
    ! [B_99,A_100] : k2_tarski(B_99,A_100) = k2_tarski(A_100,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_72])).

tff(c_78,plain,(
    ! [A_49] : k2_tarski(A_49,A_49) = k1_tarski(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_74,plain,(
    ! [A_42,B_43,C_44] : k2_xboole_0(k1_tarski(A_42),k2_tarski(B_43,C_44)) = k1_enumset1(A_42,B_43,C_44) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1040,plain,(
    ! [A_120,B_121,C_122,D_123] : k2_xboole_0(k2_tarski(A_120,B_121),k2_tarski(C_122,D_123)) = k2_enumset1(A_120,B_121,C_122,D_123) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1077,plain,(
    ! [A_49,C_122,D_123] : k2_xboole_0(k1_tarski(A_49),k2_tarski(C_122,D_123)) = k2_enumset1(A_49,A_49,C_122,D_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1040])).

tff(c_2751,plain,(
    ! [A_181,C_182,D_183] : k2_enumset1(A_181,A_181,C_182,D_183) = k1_enumset1(A_181,C_182,D_183) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1077])).

tff(c_42,plain,(
    ! [A_17] : k2_xboole_0(A_17,A_17) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1053,plain,(
    ! [C_122,D_123] : k2_enumset1(C_122,D_123,C_122,D_123) = k2_tarski(C_122,D_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_1040,c_42])).

tff(c_2758,plain,(
    ! [D_183] : k1_enumset1(D_183,D_183,D_183) = k2_tarski(D_183,D_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_1053])).

tff(c_2770,plain,(
    ! [D_184] : k1_enumset1(D_184,D_184,D_184) = k1_tarski(D_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2758])).

tff(c_76,plain,(
    ! [A_45,B_46,C_47,D_48] : k2_xboole_0(k1_enumset1(A_45,B_46,C_47),k1_tarski(D_48)) = k2_enumset1(A_45,B_46,C_47,D_48) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2776,plain,(
    ! [D_184,D_48] : k2_xboole_0(k1_tarski(D_184),k1_tarski(D_48)) = k2_enumset1(D_184,D_184,D_184,D_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_2770,c_76])).

tff(c_2807,plain,(
    ! [D_188,D_189] : k2_enumset1(D_188,D_188,D_188,D_189) = k2_tarski(D_188,D_189) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2776])).

tff(c_1087,plain,(
    ! [A_49,C_122,D_123] : k2_enumset1(A_49,A_49,C_122,D_123) = k1_enumset1(A_49,C_122,D_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1077])).

tff(c_2813,plain,(
    ! [D_188,D_189] : k1_enumset1(D_188,D_188,D_189) = k2_tarski(D_188,D_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_2807,c_1087])).

tff(c_80,plain,(
    k1_enumset1('#skF_7','#skF_7','#skF_8') != k2_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_728,plain,(
    k1_enumset1('#skF_7','#skF_7','#skF_8') != k2_tarski('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_80])).

tff(c_2833,plain,(
    k2_tarski('#skF_7','#skF_8') != k2_tarski('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2813,c_728])).

tff(c_2836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_2833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.69  
% 3.76/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.69  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5
% 3.76/1.69  
% 3.76/1.69  %Foreground sorts:
% 3.76/1.69  
% 3.76/1.69  
% 3.76/1.69  %Background operators:
% 3.76/1.69  
% 3.76/1.69  
% 3.76/1.69  %Foreground operators:
% 3.76/1.69  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.76/1.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.76/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.76/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.76/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.76/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.76/1.69  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.76/1.69  tff('#skF_7', type, '#skF_7': $i).
% 3.76/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.76/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.76/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.76/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.76/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.76/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.76/1.69  tff('#skF_8', type, '#skF_8': $i).
% 3.76/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.76/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.76/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.76/1.69  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.76/1.69  
% 3.76/1.71  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.76/1.71  tff(f_81, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.76/1.71  tff(f_87, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.76/1.71  tff(f_83, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.76/1.71  tff(f_79, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.76/1.71  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.76/1.71  tff(f_85, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.76/1.71  tff(f_90, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.76/1.71  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.76/1.71  tff(c_312, plain, (![A_71, B_72]: (k2_xboole_0(k1_tarski(A_71), k1_tarski(B_72))=k2_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.76/1.71  tff(c_687, plain, (![B_99, A_100]: (k2_xboole_0(k1_tarski(B_99), k1_tarski(A_100))=k2_tarski(A_100, B_99))), inference(superposition, [status(thm), theory('equality')], [c_2, c_312])).
% 3.76/1.71  tff(c_72, plain, (![A_40, B_41]: (k2_xboole_0(k1_tarski(A_40), k1_tarski(B_41))=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.76/1.71  tff(c_693, plain, (![B_99, A_100]: (k2_tarski(B_99, A_100)=k2_tarski(A_100, B_99))), inference(superposition, [status(thm), theory('equality')], [c_687, c_72])).
% 3.76/1.71  tff(c_78, plain, (![A_49]: (k2_tarski(A_49, A_49)=k1_tarski(A_49))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.76/1.71  tff(c_74, plain, (![A_42, B_43, C_44]: (k2_xboole_0(k1_tarski(A_42), k2_tarski(B_43, C_44))=k1_enumset1(A_42, B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.76/1.71  tff(c_1040, plain, (![A_120, B_121, C_122, D_123]: (k2_xboole_0(k2_tarski(A_120, B_121), k2_tarski(C_122, D_123))=k2_enumset1(A_120, B_121, C_122, D_123))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.76/1.71  tff(c_1077, plain, (![A_49, C_122, D_123]: (k2_xboole_0(k1_tarski(A_49), k2_tarski(C_122, D_123))=k2_enumset1(A_49, A_49, C_122, D_123))), inference(superposition, [status(thm), theory('equality')], [c_78, c_1040])).
% 3.76/1.71  tff(c_2751, plain, (![A_181, C_182, D_183]: (k2_enumset1(A_181, A_181, C_182, D_183)=k1_enumset1(A_181, C_182, D_183))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1077])).
% 3.76/1.71  tff(c_42, plain, (![A_17]: (k2_xboole_0(A_17, A_17)=A_17)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.76/1.71  tff(c_1053, plain, (![C_122, D_123]: (k2_enumset1(C_122, D_123, C_122, D_123)=k2_tarski(C_122, D_123))), inference(superposition, [status(thm), theory('equality')], [c_1040, c_42])).
% 3.76/1.71  tff(c_2758, plain, (![D_183]: (k1_enumset1(D_183, D_183, D_183)=k2_tarski(D_183, D_183))), inference(superposition, [status(thm), theory('equality')], [c_2751, c_1053])).
% 3.76/1.71  tff(c_2770, plain, (![D_184]: (k1_enumset1(D_184, D_184, D_184)=k1_tarski(D_184))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2758])).
% 3.76/1.71  tff(c_76, plain, (![A_45, B_46, C_47, D_48]: (k2_xboole_0(k1_enumset1(A_45, B_46, C_47), k1_tarski(D_48))=k2_enumset1(A_45, B_46, C_47, D_48))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.76/1.71  tff(c_2776, plain, (![D_184, D_48]: (k2_xboole_0(k1_tarski(D_184), k1_tarski(D_48))=k2_enumset1(D_184, D_184, D_184, D_48))), inference(superposition, [status(thm), theory('equality')], [c_2770, c_76])).
% 3.76/1.71  tff(c_2807, plain, (![D_188, D_189]: (k2_enumset1(D_188, D_188, D_188, D_189)=k2_tarski(D_188, D_189))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2776])).
% 3.76/1.71  tff(c_1087, plain, (![A_49, C_122, D_123]: (k2_enumset1(A_49, A_49, C_122, D_123)=k1_enumset1(A_49, C_122, D_123))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1077])).
% 3.76/1.71  tff(c_2813, plain, (![D_188, D_189]: (k1_enumset1(D_188, D_188, D_189)=k2_tarski(D_188, D_189))), inference(superposition, [status(thm), theory('equality')], [c_2807, c_1087])).
% 3.76/1.71  tff(c_80, plain, (k1_enumset1('#skF_7', '#skF_7', '#skF_8')!=k2_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.76/1.71  tff(c_728, plain, (k1_enumset1('#skF_7', '#skF_7', '#skF_8')!=k2_tarski('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_693, c_80])).
% 3.76/1.71  tff(c_2833, plain, (k2_tarski('#skF_7', '#skF_8')!=k2_tarski('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2813, c_728])).
% 3.76/1.71  tff(c_2836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_693, c_2833])).
% 3.76/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.71  
% 3.76/1.71  Inference rules
% 3.76/1.71  ----------------------
% 3.76/1.71  #Ref     : 0
% 3.76/1.71  #Sup     : 628
% 3.76/1.71  #Fact    : 0
% 3.76/1.71  #Define  : 0
% 3.76/1.71  #Split   : 0
% 3.76/1.71  #Chain   : 0
% 3.76/1.71  #Close   : 0
% 3.76/1.71  
% 3.76/1.71  Ordering : KBO
% 3.76/1.71  
% 3.76/1.71  Simplification rules
% 3.76/1.71  ----------------------
% 3.76/1.71  #Subsume      : 51
% 3.76/1.71  #Demod        : 442
% 3.76/1.71  #Tautology    : 383
% 3.76/1.71  #SimpNegUnit  : 0
% 3.76/1.71  #BackRed      : 6
% 3.76/1.71  
% 3.76/1.71  #Partial instantiations: 0
% 3.76/1.71  #Strategies tried      : 1
% 3.76/1.71  
% 3.76/1.71  Timing (in seconds)
% 3.76/1.71  ----------------------
% 4.11/1.71  Preprocessing        : 0.31
% 4.11/1.71  Parsing              : 0.16
% 4.11/1.71  CNF conversion       : 0.03
% 4.11/1.71  Main loop            : 0.61
% 4.11/1.71  Inferencing          : 0.20
% 4.11/1.71  Reduction            : 0.23
% 4.11/1.71  Demodulation         : 0.19
% 4.11/1.71  BG Simplification    : 0.03
% 4.11/1.71  Subsumption          : 0.10
% 4.11/1.71  Abstraction          : 0.03
% 4.11/1.71  MUC search           : 0.00
% 4.11/1.71  Cooper               : 0.00
% 4.11/1.71  Total                : 0.95
% 4.11/1.71  Index Insertion      : 0.00
% 4.11/1.71  Index Deletion       : 0.00
% 4.11/1.71  Index Matching       : 0.00
% 4.11/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
