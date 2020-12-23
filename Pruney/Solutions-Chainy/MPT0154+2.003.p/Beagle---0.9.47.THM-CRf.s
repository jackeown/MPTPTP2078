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
% DateTime   : Thu Dec  3 09:46:04 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 102 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   36 (  83 expanded)
%              Number of equality atoms :   35 (  82 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_523,plain,(
    ! [A_69,B_70] : k2_xboole_0(k1_tarski(A_69),k1_tarski(B_70)) = k2_tarski(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_660,plain,(
    ! [B_80,A_81] : k2_xboole_0(k1_tarski(B_80),k1_tarski(A_81)) = k2_tarski(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_2])).

tff(c_50,plain,(
    ! [A_33,B_34] : k2_xboole_0(k1_tarski(A_33),k1_tarski(B_34)) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_666,plain,(
    ! [B_80,A_81] : k2_tarski(B_80,A_81) = k2_tarski(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_50])).

tff(c_56,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k1_tarski(A_35),k2_tarski(B_36,C_37)) = k1_enumset1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1081,plain,(
    ! [A_110,B_111,C_112,D_113] : k2_xboole_0(k2_tarski(A_110,B_111),k2_tarski(C_112,D_113)) = k2_enumset1(A_110,B_111,C_112,D_113) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1118,plain,(
    ! [A_42,C_112,D_113] : k2_xboole_0(k1_tarski(A_42),k2_tarski(C_112,D_113)) = k2_enumset1(A_42,A_42,C_112,D_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1081])).

tff(c_1140,plain,(
    ! [A_116,C_117,D_118] : k2_enumset1(A_116,A_116,C_117,D_118) = k1_enumset1(A_116,C_117,D_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1118])).

tff(c_24,plain,(
    ! [A_11] : k2_xboole_0(A_11,A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1094,plain,(
    ! [C_112,D_113] : k2_enumset1(C_112,D_113,C_112,D_113) = k2_tarski(C_112,D_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_24])).

tff(c_1147,plain,(
    ! [D_118] : k1_enumset1(D_118,D_118,D_118) = k2_tarski(D_118,D_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_1094])).

tff(c_1156,plain,(
    ! [D_118] : k1_enumset1(D_118,D_118,D_118) = k1_tarski(D_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1147])).

tff(c_1275,plain,(
    ! [A_126,B_127,C_128,D_129] : k2_xboole_0(k1_enumset1(A_126,B_127,C_128),k1_tarski(D_129)) = k2_enumset1(A_126,B_127,C_128,D_129) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1290,plain,(
    ! [D_118,D_129] : k2_xboole_0(k1_tarski(D_118),k1_tarski(D_129)) = k2_enumset1(D_118,D_118,D_118,D_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_1275])).

tff(c_1310,plain,(
    ! [D_130,D_131] : k2_enumset1(D_130,D_130,D_130,D_131) = k2_tarski(D_130,D_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1290])).

tff(c_1128,plain,(
    ! [A_42,C_112,D_113] : k2_enumset1(A_42,A_42,C_112,D_113) = k1_enumset1(A_42,C_112,D_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1118])).

tff(c_1346,plain,(
    ! [D_132,D_133] : k1_enumset1(D_132,D_132,D_133) = k2_tarski(D_132,D_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_1310,c_1128])).

tff(c_799,plain,(
    ! [A_86,B_87,C_88] : k2_xboole_0(k1_tarski(A_86),k2_tarski(B_87,C_88)) = k1_enumset1(A_86,B_87,C_88) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_959,plain,(
    ! [A_99,A_100,B_101] : k2_xboole_0(k1_tarski(A_99),k2_tarski(A_100,B_101)) = k1_enumset1(A_99,B_101,A_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_799])).

tff(c_965,plain,(
    ! [A_99,B_101,A_100] : k1_enumset1(A_99,B_101,A_100) = k1_enumset1(A_99,A_100,B_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_52])).

tff(c_1359,plain,(
    ! [D_132,D_133] : k1_enumset1(D_132,D_133,D_132) = k2_tarski(D_132,D_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_1346,c_965])).

tff(c_58,plain,(
    k1_enumset1('#skF_5','#skF_5','#skF_6') != k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_701,plain,(
    k1_enumset1('#skF_5','#skF_5','#skF_6') != k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_58])).

tff(c_998,plain,(
    k1_enumset1('#skF_5','#skF_6','#skF_5') != k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_701])).

tff(c_1393,plain,(
    k2_tarski('#skF_5','#skF_6') != k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_998])).

tff(c_1396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_1393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:53:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.47  
% 3.22/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.47  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.31/1.47  
% 3.31/1.47  %Foreground sorts:
% 3.31/1.47  
% 3.31/1.47  
% 3.31/1.47  %Background operators:
% 3.31/1.47  
% 3.31/1.47  
% 3.31/1.47  %Foreground operators:
% 3.31/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.31/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.31/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.31/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.31/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.31/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.31/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.31/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.31/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.31/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.31/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.31/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.31/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.31/1.47  
% 3.31/1.49  tff(f_66, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.31/1.49  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.31/1.49  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.31/1.49  tff(f_68, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 3.31/1.49  tff(f_64, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.31/1.49  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.31/1.49  tff(f_70, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.31/1.49  tff(f_75, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.31/1.49  tff(c_523, plain, (![A_69, B_70]: (k2_xboole_0(k1_tarski(A_69), k1_tarski(B_70))=k2_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.31/1.49  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.31/1.49  tff(c_660, plain, (![B_80, A_81]: (k2_xboole_0(k1_tarski(B_80), k1_tarski(A_81))=k2_tarski(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_523, c_2])).
% 3.31/1.49  tff(c_50, plain, (![A_33, B_34]: (k2_xboole_0(k1_tarski(A_33), k1_tarski(B_34))=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.31/1.49  tff(c_666, plain, (![B_80, A_81]: (k2_tarski(B_80, A_81)=k2_tarski(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_660, c_50])).
% 3.31/1.49  tff(c_56, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.31/1.49  tff(c_52, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k1_tarski(A_35), k2_tarski(B_36, C_37))=k1_enumset1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.49  tff(c_1081, plain, (![A_110, B_111, C_112, D_113]: (k2_xboole_0(k2_tarski(A_110, B_111), k2_tarski(C_112, D_113))=k2_enumset1(A_110, B_111, C_112, D_113))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.31/1.49  tff(c_1118, plain, (![A_42, C_112, D_113]: (k2_xboole_0(k1_tarski(A_42), k2_tarski(C_112, D_113))=k2_enumset1(A_42, A_42, C_112, D_113))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1081])).
% 3.31/1.49  tff(c_1140, plain, (![A_116, C_117, D_118]: (k2_enumset1(A_116, A_116, C_117, D_118)=k1_enumset1(A_116, C_117, D_118))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1118])).
% 3.31/1.49  tff(c_24, plain, (![A_11]: (k2_xboole_0(A_11, A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.31/1.49  tff(c_1094, plain, (![C_112, D_113]: (k2_enumset1(C_112, D_113, C_112, D_113)=k2_tarski(C_112, D_113))), inference(superposition, [status(thm), theory('equality')], [c_1081, c_24])).
% 3.31/1.49  tff(c_1147, plain, (![D_118]: (k1_enumset1(D_118, D_118, D_118)=k2_tarski(D_118, D_118))), inference(superposition, [status(thm), theory('equality')], [c_1140, c_1094])).
% 3.31/1.49  tff(c_1156, plain, (![D_118]: (k1_enumset1(D_118, D_118, D_118)=k1_tarski(D_118))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1147])).
% 3.31/1.49  tff(c_1275, plain, (![A_126, B_127, C_128, D_129]: (k2_xboole_0(k1_enumset1(A_126, B_127, C_128), k1_tarski(D_129))=k2_enumset1(A_126, B_127, C_128, D_129))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.31/1.49  tff(c_1290, plain, (![D_118, D_129]: (k2_xboole_0(k1_tarski(D_118), k1_tarski(D_129))=k2_enumset1(D_118, D_118, D_118, D_129))), inference(superposition, [status(thm), theory('equality')], [c_1156, c_1275])).
% 3.31/1.49  tff(c_1310, plain, (![D_130, D_131]: (k2_enumset1(D_130, D_130, D_130, D_131)=k2_tarski(D_130, D_131))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1290])).
% 3.31/1.49  tff(c_1128, plain, (![A_42, C_112, D_113]: (k2_enumset1(A_42, A_42, C_112, D_113)=k1_enumset1(A_42, C_112, D_113))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1118])).
% 3.31/1.49  tff(c_1346, plain, (![D_132, D_133]: (k1_enumset1(D_132, D_132, D_133)=k2_tarski(D_132, D_133))), inference(superposition, [status(thm), theory('equality')], [c_1310, c_1128])).
% 3.31/1.49  tff(c_799, plain, (![A_86, B_87, C_88]: (k2_xboole_0(k1_tarski(A_86), k2_tarski(B_87, C_88))=k1_enumset1(A_86, B_87, C_88))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.49  tff(c_959, plain, (![A_99, A_100, B_101]: (k2_xboole_0(k1_tarski(A_99), k2_tarski(A_100, B_101))=k1_enumset1(A_99, B_101, A_100))), inference(superposition, [status(thm), theory('equality')], [c_666, c_799])).
% 3.31/1.49  tff(c_965, plain, (![A_99, B_101, A_100]: (k1_enumset1(A_99, B_101, A_100)=k1_enumset1(A_99, A_100, B_101))), inference(superposition, [status(thm), theory('equality')], [c_959, c_52])).
% 3.31/1.49  tff(c_1359, plain, (![D_132, D_133]: (k1_enumset1(D_132, D_133, D_132)=k2_tarski(D_132, D_133))), inference(superposition, [status(thm), theory('equality')], [c_1346, c_965])).
% 3.31/1.49  tff(c_58, plain, (k1_enumset1('#skF_5', '#skF_5', '#skF_6')!=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.31/1.49  tff(c_701, plain, (k1_enumset1('#skF_5', '#skF_5', '#skF_6')!=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_666, c_58])).
% 3.31/1.49  tff(c_998, plain, (k1_enumset1('#skF_5', '#skF_6', '#skF_5')!=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_965, c_701])).
% 3.31/1.49  tff(c_1393, plain, (k2_tarski('#skF_5', '#skF_6')!=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_998])).
% 3.31/1.49  tff(c_1396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_666, c_1393])).
% 3.31/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.49  
% 3.31/1.49  Inference rules
% 3.31/1.49  ----------------------
% 3.31/1.49  #Ref     : 0
% 3.31/1.49  #Sup     : 317
% 3.31/1.49  #Fact    : 0
% 3.31/1.49  #Define  : 0
% 3.31/1.49  #Split   : 0
% 3.31/1.49  #Chain   : 0
% 3.31/1.49  #Close   : 0
% 3.31/1.49  
% 3.31/1.49  Ordering : KBO
% 3.31/1.49  
% 3.31/1.49  Simplification rules
% 3.31/1.49  ----------------------
% 3.31/1.49  #Subsume      : 9
% 3.31/1.49  #Demod        : 165
% 3.31/1.49  #Tautology    : 235
% 3.31/1.49  #SimpNegUnit  : 0
% 3.31/1.49  #BackRed      : 3
% 3.31/1.49  
% 3.31/1.49  #Partial instantiations: 0
% 3.31/1.49  #Strategies tried      : 1
% 3.31/1.49  
% 3.31/1.49  Timing (in seconds)
% 3.31/1.49  ----------------------
% 3.31/1.49  Preprocessing        : 0.33
% 3.31/1.49  Parsing              : 0.17
% 3.31/1.49  CNF conversion       : 0.02
% 3.31/1.49  Main loop            : 0.40
% 3.31/1.49  Inferencing          : 0.14
% 3.31/1.49  Reduction            : 0.15
% 3.31/1.49  Demodulation         : 0.12
% 3.31/1.49  BG Simplification    : 0.02
% 3.31/1.49  Subsumption          : 0.06
% 3.31/1.49  Abstraction          : 0.02
% 3.31/1.49  MUC search           : 0.00
% 3.31/1.49  Cooper               : 0.00
% 3.31/1.49  Total                : 0.76
% 3.31/1.49  Index Insertion      : 0.00
% 3.31/1.49  Index Deletion       : 0.00
% 3.31/1.49  Index Matching       : 0.00
% 3.31/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
