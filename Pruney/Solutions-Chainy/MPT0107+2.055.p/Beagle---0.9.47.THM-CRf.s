%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:00 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86,plain,(
    ! [A_24,B_25] : k2_xboole_0(k3_xboole_0(A_24,B_25),k4_xboole_0(A_24,B_25)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_195,plain,(
    ! [A_31,B_32] : k4_xboole_0(k3_xboole_0(A_31,B_32),A_31) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_203,plain,(
    ! [A_31,B_32] : k2_xboole_0(k4_xboole_0(A_31,k3_xboole_0(A_31,B_32)),k1_xboole_0) = k5_xboole_0(A_31,k3_xboole_0(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_2])).

tff(c_222,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6,c_203])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.41  
% 2.23/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.41  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.23/1.41  
% 2.23/1.41  %Foreground sorts:
% 2.23/1.41  
% 2.23/1.41  
% 2.23/1.41  %Background operators:
% 2.23/1.41  
% 2.23/1.41  
% 2.23/1.41  %Foreground operators:
% 2.23/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.41  
% 2.23/1.42  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.23/1.42  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.23/1.42  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.23/1.42  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.23/1.42  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.23/1.42  tff(f_46, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.23/1.42  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.23/1.42  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.42  tff(c_86, plain, (![A_24, B_25]: (k2_xboole_0(k3_xboole_0(A_24, B_25), k4_xboole_0(A_24, B_25))=A_24)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.23/1.42  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.42  tff(c_195, plain, (![A_31, B_32]: (k4_xboole_0(k3_xboole_0(A_31, B_32), A_31)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_86, c_10])).
% 2.23/1.42  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.42  tff(c_203, plain, (![A_31, B_32]: (k2_xboole_0(k4_xboole_0(A_31, k3_xboole_0(A_31, B_32)), k1_xboole_0)=k5_xboole_0(A_31, k3_xboole_0(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_195, c_2])).
% 2.23/1.42  tff(c_222, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6, c_203])).
% 2.23/1.42  tff(c_18, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.42  tff(c_663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_222, c_18])).
% 2.23/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.42  
% 2.23/1.42  Inference rules
% 2.23/1.42  ----------------------
% 2.23/1.42  #Ref     : 0
% 2.23/1.42  #Sup     : 159
% 2.23/1.42  #Fact    : 0
% 2.23/1.42  #Define  : 0
% 2.23/1.42  #Split   : 1
% 2.23/1.42  #Chain   : 0
% 2.23/1.42  #Close   : 0
% 2.23/1.42  
% 2.23/1.42  Ordering : KBO
% 2.23/1.42  
% 2.23/1.42  Simplification rules
% 2.23/1.42  ----------------------
% 2.23/1.42  #Subsume      : 5
% 2.23/1.42  #Demod        : 78
% 2.23/1.42  #Tautology    : 116
% 2.23/1.42  #SimpNegUnit  : 0
% 2.23/1.42  #BackRed      : 4
% 2.23/1.42  
% 2.23/1.42  #Partial instantiations: 0
% 2.23/1.42  #Strategies tried      : 1
% 2.23/1.42  
% 2.23/1.42  Timing (in seconds)
% 2.23/1.42  ----------------------
% 2.23/1.42  Preprocessing        : 0.33
% 2.23/1.42  Parsing              : 0.17
% 2.23/1.42  CNF conversion       : 0.02
% 2.23/1.42  Main loop            : 0.27
% 2.23/1.42  Inferencing          : 0.10
% 2.23/1.42  Reduction            : 0.09
% 2.23/1.42  Demodulation         : 0.07
% 2.23/1.42  BG Simplification    : 0.02
% 2.23/1.42  Subsumption          : 0.04
% 2.23/1.42  Abstraction          : 0.02
% 2.23/1.42  MUC search           : 0.00
% 2.23/1.42  Cooper               : 0.00
% 2.23/1.42  Total                : 0.63
% 2.23/1.42  Index Insertion      : 0.00
% 2.23/1.42  Index Deletion       : 0.00
% 2.23/1.42  Index Matching       : 0.00
% 2.23/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
