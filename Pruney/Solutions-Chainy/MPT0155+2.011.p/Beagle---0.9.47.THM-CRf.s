%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:10 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   48 (  83 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   30 (  65 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_14,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_xboole_0(k1_tarski(A_19),k1_enumset1(B_20,C_21,D_22)) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_70] : k2_tarski(A_70,A_70) = k1_tarski(A_70) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_188,plain,(
    ! [A_87,B_88,C_89] : k2_xboole_0(k1_tarski(A_87),k2_tarski(B_88,C_89)) = k1_enumset1(A_87,B_88,C_89) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_200,plain,(
    ! [A_90,A_91] : k2_xboole_0(k1_tarski(A_90),k1_tarski(A_91)) = k1_enumset1(A_90,A_91,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_188])).

tff(c_32,plain,(
    ! [A_71,B_72] : k1_enumset1(A_71,A_71,B_72) = k2_tarski(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_210,plain,(
    ! [A_91] : k2_xboole_0(k1_tarski(A_91),k1_tarski(A_91)) = k2_tarski(A_91,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_32])).

tff(c_227,plain,(
    ! [A_92] : k2_xboole_0(k1_tarski(A_92),k1_tarski(A_92)) = k1_tarski(A_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_210])).

tff(c_197,plain,(
    ! [A_87,A_70] : k2_xboole_0(k1_tarski(A_87),k1_tarski(A_70)) = k1_enumset1(A_87,A_70,A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_188])).

tff(c_233,plain,(
    ! [A_92] : k1_enumset1(A_92,A_92,A_92) = k1_tarski(A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_197])).

tff(c_569,plain,(
    ! [A_124,B_122,E_123,D_125,F_126,C_127] : k2_xboole_0(k1_enumset1(A_124,B_122,C_127),k1_enumset1(D_125,E_123,F_126)) = k4_enumset1(A_124,B_122,C_127,D_125,E_123,F_126) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_578,plain,(
    ! [A_92,D_125,E_123,F_126] : k4_enumset1(A_92,A_92,A_92,D_125,E_123,F_126) = k2_xboole_0(k1_tarski(A_92),k1_enumset1(D_125,E_123,F_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_569])).

tff(c_849,plain,(
    ! [A_158,D_159,E_160,F_161] : k4_enumset1(A_158,A_158,A_158,D_159,E_160,F_161) = k2_enumset1(A_158,D_159,E_160,F_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_578])).

tff(c_12,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k1_tarski(A_16),k2_tarski(B_17,C_18)) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_272,plain,(
    ! [A_94,B_95,C_96,D_97] : k2_xboole_0(k1_tarski(A_94),k1_enumset1(B_95,C_96,D_97)) = k2_enumset1(A_94,B_95,C_96,D_97) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_300,plain,(
    ! [A_101,A_102] : k2_xboole_0(k1_tarski(A_101),k1_tarski(A_102)) = k2_enumset1(A_101,A_102,A_102,A_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_272])).

tff(c_223,plain,(
    ! [A_91] : k2_xboole_0(k1_tarski(A_91),k1_tarski(A_91)) = k1_tarski(A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_210])).

tff(c_313,plain,(
    ! [A_102] : k2_enumset1(A_102,A_102,A_102,A_102) = k1_tarski(A_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_223])).

tff(c_630,plain,(
    ! [E_132,A_133,F_131,D_136,C_134,B_135] : k2_xboole_0(k2_enumset1(A_133,B_135,C_134,D_136),k2_tarski(E_132,F_131)) = k4_enumset1(A_133,B_135,C_134,D_136,E_132,F_131) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_639,plain,(
    ! [A_102,E_132,F_131] : k4_enumset1(A_102,A_102,A_102,A_102,E_132,F_131) = k2_xboole_0(k1_tarski(A_102),k2_tarski(E_132,F_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_630])).

tff(c_651,plain,(
    ! [A_102,E_132,F_131] : k4_enumset1(A_102,A_102,A_102,A_102,E_132,F_131) = k1_enumset1(A_102,E_132,F_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_639])).

tff(c_856,plain,(
    ! [D_159,E_160,F_161] : k2_enumset1(D_159,D_159,E_160,F_161) = k1_enumset1(D_159,E_160,F_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_651])).

tff(c_34,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:34:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.39  
% 2.82/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.40  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.82/1.40  
% 2.82/1.40  %Foreground sorts:
% 2.82/1.40  
% 2.82/1.40  
% 2.82/1.40  %Background operators:
% 2.82/1.40  
% 2.82/1.40  
% 2.82/1.40  %Foreground operators:
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.82/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.82/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.82/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.82/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.82/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.82/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.82/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.40  
% 2.82/1.41  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.82/1.41  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.82/1.41  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.82/1.41  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.82/1.41  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 2.82/1.41  tff(f_43, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 2.82/1.41  tff(f_60, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.82/1.41  tff(c_14, plain, (![A_19, B_20, C_21, D_22]: (k2_xboole_0(k1_tarski(A_19), k1_enumset1(B_20, C_21, D_22))=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.82/1.41  tff(c_30, plain, (![A_70]: (k2_tarski(A_70, A_70)=k1_tarski(A_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.82/1.41  tff(c_188, plain, (![A_87, B_88, C_89]: (k2_xboole_0(k1_tarski(A_87), k2_tarski(B_88, C_89))=k1_enumset1(A_87, B_88, C_89))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.41  tff(c_200, plain, (![A_90, A_91]: (k2_xboole_0(k1_tarski(A_90), k1_tarski(A_91))=k1_enumset1(A_90, A_91, A_91))), inference(superposition, [status(thm), theory('equality')], [c_30, c_188])).
% 2.82/1.41  tff(c_32, plain, (![A_71, B_72]: (k1_enumset1(A_71, A_71, B_72)=k2_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.41  tff(c_210, plain, (![A_91]: (k2_xboole_0(k1_tarski(A_91), k1_tarski(A_91))=k2_tarski(A_91, A_91))), inference(superposition, [status(thm), theory('equality')], [c_200, c_32])).
% 2.82/1.41  tff(c_227, plain, (![A_92]: (k2_xboole_0(k1_tarski(A_92), k1_tarski(A_92))=k1_tarski(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_210])).
% 2.82/1.41  tff(c_197, plain, (![A_87, A_70]: (k2_xboole_0(k1_tarski(A_87), k1_tarski(A_70))=k1_enumset1(A_87, A_70, A_70))), inference(superposition, [status(thm), theory('equality')], [c_30, c_188])).
% 2.82/1.41  tff(c_233, plain, (![A_92]: (k1_enumset1(A_92, A_92, A_92)=k1_tarski(A_92))), inference(superposition, [status(thm), theory('equality')], [c_227, c_197])).
% 2.82/1.41  tff(c_569, plain, (![A_124, B_122, E_123, D_125, F_126, C_127]: (k2_xboole_0(k1_enumset1(A_124, B_122, C_127), k1_enumset1(D_125, E_123, F_126))=k4_enumset1(A_124, B_122, C_127, D_125, E_123, F_126))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.41  tff(c_578, plain, (![A_92, D_125, E_123, F_126]: (k4_enumset1(A_92, A_92, A_92, D_125, E_123, F_126)=k2_xboole_0(k1_tarski(A_92), k1_enumset1(D_125, E_123, F_126)))), inference(superposition, [status(thm), theory('equality')], [c_233, c_569])).
% 2.82/1.41  tff(c_849, plain, (![A_158, D_159, E_160, F_161]: (k4_enumset1(A_158, A_158, A_158, D_159, E_160, F_161)=k2_enumset1(A_158, D_159, E_160, F_161))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_578])).
% 2.82/1.41  tff(c_12, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k1_tarski(A_16), k2_tarski(B_17, C_18))=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.41  tff(c_272, plain, (![A_94, B_95, C_96, D_97]: (k2_xboole_0(k1_tarski(A_94), k1_enumset1(B_95, C_96, D_97))=k2_enumset1(A_94, B_95, C_96, D_97))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.82/1.41  tff(c_300, plain, (![A_101, A_102]: (k2_xboole_0(k1_tarski(A_101), k1_tarski(A_102))=k2_enumset1(A_101, A_102, A_102, A_102))), inference(superposition, [status(thm), theory('equality')], [c_233, c_272])).
% 2.82/1.41  tff(c_223, plain, (![A_91]: (k2_xboole_0(k1_tarski(A_91), k1_tarski(A_91))=k1_tarski(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_210])).
% 2.82/1.41  tff(c_313, plain, (![A_102]: (k2_enumset1(A_102, A_102, A_102, A_102)=k1_tarski(A_102))), inference(superposition, [status(thm), theory('equality')], [c_300, c_223])).
% 2.82/1.41  tff(c_630, plain, (![E_132, A_133, F_131, D_136, C_134, B_135]: (k2_xboole_0(k2_enumset1(A_133, B_135, C_134, D_136), k2_tarski(E_132, F_131))=k4_enumset1(A_133, B_135, C_134, D_136, E_132, F_131))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.82/1.41  tff(c_639, plain, (![A_102, E_132, F_131]: (k4_enumset1(A_102, A_102, A_102, A_102, E_132, F_131)=k2_xboole_0(k1_tarski(A_102), k2_tarski(E_132, F_131)))), inference(superposition, [status(thm), theory('equality')], [c_313, c_630])).
% 2.82/1.41  tff(c_651, plain, (![A_102, E_132, F_131]: (k4_enumset1(A_102, A_102, A_102, A_102, E_132, F_131)=k1_enumset1(A_102, E_132, F_131))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_639])).
% 2.82/1.41  tff(c_856, plain, (![D_159, E_160, F_161]: (k2_enumset1(D_159, D_159, E_160, F_161)=k1_enumset1(D_159, E_160, F_161))), inference(superposition, [status(thm), theory('equality')], [c_849, c_651])).
% 2.82/1.41  tff(c_34, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.41  tff(c_867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_856, c_34])).
% 2.82/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.41  
% 2.82/1.41  Inference rules
% 2.82/1.41  ----------------------
% 2.82/1.41  #Ref     : 0
% 2.82/1.41  #Sup     : 203
% 2.82/1.41  #Fact    : 0
% 2.82/1.41  #Define  : 0
% 2.82/1.41  #Split   : 0
% 2.82/1.41  #Chain   : 0
% 2.82/1.41  #Close   : 0
% 2.82/1.41  
% 2.82/1.41  Ordering : KBO
% 2.82/1.41  
% 2.82/1.41  Simplification rules
% 2.82/1.41  ----------------------
% 2.82/1.41  #Subsume      : 10
% 2.82/1.41  #Demod        : 80
% 2.82/1.41  #Tautology    : 119
% 2.82/1.41  #SimpNegUnit  : 0
% 2.82/1.41  #BackRed      : 1
% 2.82/1.41  
% 2.82/1.41  #Partial instantiations: 0
% 2.82/1.41  #Strategies tried      : 1
% 2.82/1.41  
% 2.82/1.41  Timing (in seconds)
% 2.82/1.41  ----------------------
% 2.82/1.41  Preprocessing        : 0.33
% 2.82/1.41  Parsing              : 0.17
% 2.82/1.41  CNF conversion       : 0.02
% 2.82/1.41  Main loop            : 0.31
% 2.82/1.41  Inferencing          : 0.12
% 2.82/1.41  Reduction            : 0.11
% 2.82/1.41  Demodulation         : 0.09
% 2.82/1.41  BG Simplification    : 0.03
% 2.82/1.41  Subsumption          : 0.04
% 2.82/1.41  Abstraction          : 0.02
% 2.82/1.41  MUC search           : 0.00
% 2.82/1.41  Cooper               : 0.00
% 2.82/1.41  Total                : 0.66
% 2.82/1.41  Index Insertion      : 0.00
% 2.82/1.41  Index Deletion       : 0.00
% 2.82/1.41  Index Matching       : 0.00
% 2.82/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
