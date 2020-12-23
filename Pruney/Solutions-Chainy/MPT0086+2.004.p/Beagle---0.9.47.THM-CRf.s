%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:14 EST 2020

% Result     : Theorem 5.08s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :   41 (  75 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   33 (  67 expanded)
%              Number of equality atoms :   28 (  62 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_128,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_110])).

tff(c_135,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_128])).

tff(c_203,plain,(
    ! [A_35,B_36] : k2_xboole_0(k3_xboole_0(A_35,B_36),k4_xboole_0(A_35,B_36)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_242,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)),k1_xboole_0) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_203])).

tff(c_253,plain,(
    ! [A_37] : k2_xboole_0(A_37,k1_xboole_0) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_242])).

tff(c_274,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_14])).

tff(c_252,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_242])).

tff(c_394,plain,(
    ! [A_41] : k4_xboole_0(A_41,A_41) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_14])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_399,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_xboole_0) = k2_xboole_0(A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_8])).

tff(c_417,plain,(
    ! [A_41] : k2_xboole_0(A_41,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_399])).

tff(c_423,plain,(
    ! [A_42,B_43,C_44] : k4_xboole_0(k4_xboole_0(A_42,B_43),C_44) = k4_xboole_0(A_42,k2_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7509,plain,(
    ! [A_151,B_152,C_153] : k4_xboole_0(k4_xboole_0(A_151,B_152),k4_xboole_0(A_151,k2_xboole_0(B_152,C_153))) = k3_xboole_0(k4_xboole_0(A_151,B_152),C_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_16])).

tff(c_7718,plain,(
    ! [A_151,A_41] : k4_xboole_0(k4_xboole_0(A_151,A_41),k4_xboole_0(A_151,A_41)) = k3_xboole_0(k4_xboole_0(A_151,A_41),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_7509])).

tff(c_7843,plain,(
    ! [A_151,A_41] : k3_xboole_0(k4_xboole_0(A_151,A_41),A_41) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_7718])).

tff(c_101,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_109,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_20])).

tff(c_7863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7843,c_109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:29:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.08/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/2.09  
% 5.08/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/2.10  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 5.08/2.10  
% 5.08/2.10  %Foreground sorts:
% 5.08/2.10  
% 5.08/2.10  
% 5.08/2.10  %Background operators:
% 5.08/2.10  
% 5.08/2.10  
% 5.08/2.10  %Foreground operators:
% 5.08/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.08/2.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.08/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.08/2.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.08/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.08/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.08/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.08/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.08/2.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.08/2.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.08/2.10  
% 5.14/2.11  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.14/2.11  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.14/2.11  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.14/2.11  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.14/2.11  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.14/2.11  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.14/2.11  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.14/2.11  tff(f_46, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.14/2.11  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.14/2.11  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.14/2.11  tff(c_110, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.14/2.11  tff(c_128, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_110])).
% 5.14/2.11  tff(c_135, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_128])).
% 5.14/2.11  tff(c_203, plain, (![A_35, B_36]: (k2_xboole_0(k3_xboole_0(A_35, B_36), k4_xboole_0(A_35, B_36))=A_35)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.14/2.11  tff(c_242, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, k2_xboole_0(A_11, B_12)), k1_xboole_0)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_14, c_203])).
% 5.14/2.11  tff(c_253, plain, (![A_37]: (k2_xboole_0(A_37, k1_xboole_0)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_242])).
% 5.14/2.11  tff(c_274, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_253, c_14])).
% 5.14/2.11  tff(c_252, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_242])).
% 5.14/2.11  tff(c_394, plain, (![A_41]: (k4_xboole_0(A_41, A_41)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_253, c_14])).
% 5.14/2.11  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.14/2.11  tff(c_399, plain, (![A_41]: (k2_xboole_0(A_41, k1_xboole_0)=k2_xboole_0(A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_394, c_8])).
% 5.14/2.11  tff(c_417, plain, (![A_41]: (k2_xboole_0(A_41, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_252, c_399])).
% 5.14/2.11  tff(c_423, plain, (![A_42, B_43, C_44]: (k4_xboole_0(k4_xboole_0(A_42, B_43), C_44)=k4_xboole_0(A_42, k2_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.14/2.11  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.14/2.11  tff(c_7509, plain, (![A_151, B_152, C_153]: (k4_xboole_0(k4_xboole_0(A_151, B_152), k4_xboole_0(A_151, k2_xboole_0(B_152, C_153)))=k3_xboole_0(k4_xboole_0(A_151, B_152), C_153))), inference(superposition, [status(thm), theory('equality')], [c_423, c_16])).
% 5.14/2.11  tff(c_7718, plain, (![A_151, A_41]: (k4_xboole_0(k4_xboole_0(A_151, A_41), k4_xboole_0(A_151, A_41))=k3_xboole_0(k4_xboole_0(A_151, A_41), A_41))), inference(superposition, [status(thm), theory('equality')], [c_417, c_7509])).
% 5.14/2.11  tff(c_7843, plain, (![A_151, A_41]: (k3_xboole_0(k4_xboole_0(A_151, A_41), A_41)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_274, c_7718])).
% 5.14/2.11  tff(c_101, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/2.11  tff(c_20, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.14/2.11  tff(c_109, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_101, c_20])).
% 5.14/2.11  tff(c_7863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7843, c_109])).
% 5.14/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/2.11  
% 5.14/2.11  Inference rules
% 5.14/2.11  ----------------------
% 5.14/2.11  #Ref     : 0
% 5.14/2.11  #Sup     : 1934
% 5.14/2.11  #Fact    : 0
% 5.14/2.11  #Define  : 0
% 5.14/2.11  #Split   : 0
% 5.14/2.11  #Chain   : 0
% 5.14/2.11  #Close   : 0
% 5.14/2.11  
% 5.14/2.11  Ordering : KBO
% 5.14/2.11  
% 5.14/2.11  Simplification rules
% 5.14/2.11  ----------------------
% 5.14/2.11  #Subsume      : 0
% 5.14/2.11  #Demod        : 2183
% 5.14/2.11  #Tautology    : 1434
% 5.14/2.11  #SimpNegUnit  : 0
% 5.14/2.11  #BackRed      : 2
% 5.14/2.11  
% 5.14/2.11  #Partial instantiations: 0
% 5.14/2.11  #Strategies tried      : 1
% 5.14/2.11  
% 5.14/2.11  Timing (in seconds)
% 5.14/2.11  ----------------------
% 5.14/2.11  Preprocessing        : 0.28
% 5.14/2.11  Parsing              : 0.16
% 5.14/2.11  CNF conversion       : 0.02
% 5.18/2.11  Main loop            : 0.99
% 5.18/2.11  Inferencing          : 0.28
% 5.18/2.11  Reduction            : 0.51
% 5.18/2.11  Demodulation         : 0.44
% 5.18/2.11  BG Simplification    : 0.03
% 5.18/2.11  Subsumption          : 0.11
% 5.18/2.11  Abstraction          : 0.06
% 5.18/2.11  MUC search           : 0.00
% 5.18/2.11  Cooper               : 0.00
% 5.18/2.11  Total                : 1.29
% 5.18/2.11  Index Insertion      : 0.00
% 5.18/2.11  Index Deletion       : 0.00
% 5.18/2.11  Index Matching       : 0.00
% 5.18/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
