%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:00 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  33 expanded)
%              Number of equality atoms :   23 (  27 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_194,plain,(
    ! [A_32,B_33] : r1_tarski(k3_xboole_0(A_32,B_33),A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_304,plain,(
    ! [A_40,B_41] : k4_xboole_0(k3_xboole_0(A_40,B_41),A_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_194,c_4])).

tff(c_16,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_309,plain,(
    ! [A_40,B_41] : k2_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = k5_xboole_0(A_40,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_16])).

tff(c_327,plain,(
    ! [A_40,B_41] : k2_xboole_0(A_40,k3_xboole_0(A_40,B_41)) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_309])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_203,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k3_xboole_0(A_34,B_35)) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_212,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,k3_xboole_0(A_34,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_12])).

tff(c_780,plain,(
    ! [A_61,B_62] : k3_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_212])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_792,plain,(
    ! [A_61,B_62] : k4_xboole_0(k2_xboole_0(A_61,k3_xboole_0(A_61,B_62)),k3_xboole_0(A_61,B_62)) = k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_6])).

tff(c_828,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_327,c_792])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:40:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.51  
% 2.62/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.51  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.62/1.51  
% 2.62/1.51  %Foreground sorts:
% 2.62/1.51  
% 2.62/1.51  
% 2.62/1.51  %Background operators:
% 2.62/1.51  
% 2.62/1.51  
% 2.62/1.51  %Foreground operators:
% 2.62/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.62/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.62/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.62/1.51  
% 2.62/1.52  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.62/1.52  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.62/1.52  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.62/1.52  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.62/1.52  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.62/1.52  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.62/1.52  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 2.62/1.52  tff(f_44, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.62/1.52  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.52  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.62/1.52  tff(c_113, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.52  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.52  tff(c_194, plain, (![A_32, B_33]: (r1_tarski(k3_xboole_0(A_32, B_33), A_32))), inference(superposition, [status(thm), theory('equality')], [c_113, c_8])).
% 2.62/1.52  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.52  tff(c_304, plain, (![A_40, B_41]: (k4_xboole_0(k3_xboole_0(A_40, B_41), A_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_194, c_4])).
% 2.62/1.52  tff(c_16, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.62/1.52  tff(c_309, plain, (![A_40, B_41]: (k2_xboole_0(A_40, k3_xboole_0(A_40, B_41))=k5_xboole_0(A_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_304, c_16])).
% 2.62/1.52  tff(c_327, plain, (![A_40, B_41]: (k2_xboole_0(A_40, k3_xboole_0(A_40, B_41))=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_309])).
% 2.62/1.52  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.52  tff(c_203, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k3_xboole_0(A_34, B_35))=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.52  tff(c_212, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, k3_xboole_0(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_203, c_12])).
% 2.62/1.52  tff(c_780, plain, (![A_61, B_62]: (k3_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_212])).
% 2.62/1.52  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.52  tff(c_792, plain, (![A_61, B_62]: (k4_xboole_0(k2_xboole_0(A_61, k3_xboole_0(A_61, B_62)), k3_xboole_0(A_61, B_62))=k5_xboole_0(A_61, k3_xboole_0(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_780, c_6])).
% 2.62/1.52  tff(c_828, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_327, c_792])).
% 2.62/1.52  tff(c_18, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.62/1.52  tff(c_1024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_828, c_18])).
% 2.62/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.52  
% 2.62/1.52  Inference rules
% 2.62/1.52  ----------------------
% 2.62/1.52  #Ref     : 0
% 2.62/1.52  #Sup     : 248
% 2.62/1.52  #Fact    : 0
% 2.62/1.52  #Define  : 0
% 2.62/1.52  #Split   : 0
% 2.62/1.52  #Chain   : 0
% 2.62/1.52  #Close   : 0
% 2.62/1.52  
% 2.62/1.52  Ordering : KBO
% 2.62/1.52  
% 2.62/1.52  Simplification rules
% 2.62/1.52  ----------------------
% 2.62/1.52  #Subsume      : 0
% 2.62/1.52  #Demod        : 208
% 2.62/1.52  #Tautology    : 200
% 2.62/1.52  #SimpNegUnit  : 0
% 2.62/1.52  #BackRed      : 2
% 2.62/1.52  
% 2.62/1.52  #Partial instantiations: 0
% 2.62/1.52  #Strategies tried      : 1
% 2.62/1.52  
% 2.62/1.52  Timing (in seconds)
% 2.62/1.52  ----------------------
% 2.66/1.52  Preprocessing        : 0.37
% 2.66/1.52  Parsing              : 0.23
% 2.66/1.52  CNF conversion       : 0.02
% 2.66/1.52  Main loop            : 0.30
% 2.66/1.53  Inferencing          : 0.12
% 2.66/1.53  Reduction            : 0.11
% 2.66/1.53  Demodulation         : 0.08
% 2.66/1.53  BG Simplification    : 0.01
% 2.66/1.53  Subsumption          : 0.04
% 2.66/1.53  Abstraction          : 0.02
% 2.66/1.53  MUC search           : 0.00
% 2.66/1.53  Cooper               : 0.00
% 2.66/1.53  Total                : 0.70
% 2.66/1.53  Index Insertion      : 0.00
% 2.66/1.53  Index Deletion       : 0.00
% 2.66/1.53  Index Matching       : 0.00
% 2.66/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
