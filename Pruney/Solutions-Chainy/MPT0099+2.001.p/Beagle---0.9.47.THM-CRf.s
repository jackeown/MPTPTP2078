%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:36 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   28 (  42 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  34 expanded)
%              Number of equality atoms :   19 (  33 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_40,negated_conjecture,(
    ~ ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_50,plain,(
    ! [B_14,A_15] : k2_xboole_0(B_14,A_15) = k2_xboole_0(A_15,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    ! [A_18] : k2_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(k2_xboole_0(A_8,B_9),B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,(
    ! [A_18] : k4_xboole_0(k1_xboole_0,A_18) = k4_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_10])).

tff(c_161,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_126])).

tff(c_66,plain,(
    ! [A_15] : k2_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_220,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_126])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_225,plain,(
    ! [A_21] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_21,A_21)) = k5_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_4])).

tff(c_238,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_66,c_225])).

tff(c_14,plain,(
    k5_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n006.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:31:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.23  
% 1.81/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.23  %$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.94/1.23  
% 1.94/1.23  %Foreground sorts:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Background operators:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Foreground operators:
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.94/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.94/1.23  
% 1.94/1.24  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.94/1.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.94/1.24  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.94/1.24  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.94/1.24  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.94/1.24  tff(f_40, negated_conjecture, ~(![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.94/1.24  tff(c_12, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.24  tff(c_50, plain, (![B_14, A_15]: (k2_xboole_0(B_14, A_15)=k2_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.24  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.24  tff(c_120, plain, (![A_18]: (k2_xboole_0(k1_xboole_0, A_18)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_50, c_8])).
% 1.94/1.24  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(k2_xboole_0(A_8, B_9), B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.24  tff(c_126, plain, (![A_18]: (k4_xboole_0(k1_xboole_0, A_18)=k4_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_120, c_10])).
% 1.94/1.24  tff(c_161, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_126])).
% 1.94/1.24  tff(c_66, plain, (![A_15]: (k2_xboole_0(k1_xboole_0, A_15)=A_15)), inference(superposition, [status(thm), theory('equality')], [c_50, c_8])).
% 1.94/1.24  tff(c_220, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_126])).
% 1.94/1.24  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.24  tff(c_225, plain, (![A_21]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_21, A_21))=k5_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_220, c_4])).
% 1.94/1.24  tff(c_238, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_66, c_225])).
% 1.94/1.24  tff(c_14, plain, (k5_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.94/1.24  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_238, c_14])).
% 1.94/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  Inference rules
% 1.94/1.24  ----------------------
% 1.94/1.24  #Ref     : 0
% 1.94/1.24  #Sup     : 56
% 1.94/1.24  #Fact    : 0
% 1.94/1.24  #Define  : 0
% 1.94/1.24  #Split   : 0
% 1.94/1.24  #Chain   : 0
% 1.94/1.24  #Close   : 0
% 1.94/1.24  
% 1.94/1.24  Ordering : KBO
% 1.94/1.24  
% 1.94/1.24  Simplification rules
% 1.94/1.24  ----------------------
% 1.94/1.24  #Subsume      : 0
% 1.94/1.24  #Demod        : 15
% 1.94/1.24  #Tautology    : 39
% 1.94/1.24  #SimpNegUnit  : 0
% 1.94/1.24  #BackRed      : 1
% 1.94/1.24  
% 1.94/1.24  #Partial instantiations: 0
% 1.94/1.24  #Strategies tried      : 1
% 1.94/1.24  
% 1.94/1.24  Timing (in seconds)
% 1.94/1.24  ----------------------
% 1.94/1.24  Preprocessing        : 0.27
% 1.94/1.24  Parsing              : 0.15
% 1.94/1.24  CNF conversion       : 0.01
% 1.94/1.24  Main loop            : 0.14
% 1.94/1.24  Inferencing          : 0.06
% 1.94/1.24  Reduction            : 0.05
% 1.94/1.24  Demodulation         : 0.04
% 1.94/1.24  BG Simplification    : 0.01
% 1.94/1.24  Subsumption          : 0.02
% 1.94/1.24  Abstraction          : 0.01
% 1.94/1.24  MUC search           : 0.00
% 1.94/1.24  Cooper               : 0.00
% 1.94/1.24  Total                : 0.44
% 1.94/1.24  Index Insertion      : 0.00
% 1.94/1.24  Index Deletion       : 0.00
% 1.94/1.24  Index Matching       : 0.00
% 1.94/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
