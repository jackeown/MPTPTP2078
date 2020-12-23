%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:26 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_120,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_120])).

tff(c_160,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_160])).

tff(c_185,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_176])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : r1_tarski(k3_xboole_0(A_6,B_7),k2_xboole_0(A_6,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_203,plain,(
    ! [B_7] : r1_tarski(k3_xboole_0('#skF_1',B_7),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_10])).

tff(c_16,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:36:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.27  
% 1.85/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.27  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.85/1.27  
% 1.85/1.27  %Foreground sorts:
% 1.85/1.27  
% 1.85/1.27  
% 1.85/1.27  %Background operators:
% 1.85/1.27  
% 1.85/1.27  
% 1.85/1.27  %Foreground operators:
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.85/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.27  
% 1.85/1.28  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.85/1.28  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.85/1.28  tff(f_44, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.85/1.28  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.85/1.28  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.85/1.28  tff(f_35, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 1.85/1.28  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.85/1.28  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.85/1.28  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.28  tff(c_120, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.28  tff(c_128, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_120])).
% 1.85/1.28  tff(c_160, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.85/1.28  tff(c_176, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_128, c_160])).
% 1.85/1.28  tff(c_185, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_176])).
% 1.85/1.28  tff(c_10, plain, (![A_6, B_7, C_8]: (r1_tarski(k3_xboole_0(A_6, B_7), k2_xboole_0(A_6, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.85/1.28  tff(c_203, plain, (![B_7]: (r1_tarski(k3_xboole_0('#skF_1', B_7), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_10])).
% 1.85/1.28  tff(c_16, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.28  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_16])).
% 1.85/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.28  
% 1.85/1.28  Inference rules
% 1.85/1.29  ----------------------
% 1.85/1.29  #Ref     : 0
% 1.85/1.29  #Sup     : 46
% 1.85/1.29  #Fact    : 0
% 1.85/1.29  #Define  : 0
% 1.85/1.29  #Split   : 0
% 1.85/1.29  #Chain   : 0
% 1.85/1.29  #Close   : 0
% 1.85/1.29  
% 1.85/1.29  Ordering : KBO
% 1.85/1.29  
% 1.85/1.29  Simplification rules
% 1.85/1.29  ----------------------
% 1.85/1.29  #Subsume      : 0
% 1.85/1.29  #Demod        : 16
% 1.85/1.29  #Tautology    : 33
% 1.85/1.29  #SimpNegUnit  : 0
% 1.85/1.29  #BackRed      : 1
% 1.85/1.29  
% 1.85/1.29  #Partial instantiations: 0
% 1.85/1.29  #Strategies tried      : 1
% 1.85/1.29  
% 1.85/1.29  Timing (in seconds)
% 1.85/1.29  ----------------------
% 1.85/1.29  Preprocessing        : 0.25
% 1.85/1.29  Parsing              : 0.14
% 1.85/1.29  CNF conversion       : 0.02
% 1.85/1.29  Main loop            : 0.19
% 1.85/1.29  Inferencing          : 0.08
% 1.85/1.29  Reduction            : 0.06
% 1.85/1.29  Demodulation         : 0.05
% 1.85/1.29  BG Simplification    : 0.01
% 1.85/1.29  Subsumption          : 0.02
% 1.85/1.29  Abstraction          : 0.01
% 1.85/1.29  MUC search           : 0.00
% 1.85/1.29  Cooper               : 0.00
% 1.85/1.29  Total                : 0.47
% 1.85/1.29  Index Insertion      : 0.00
% 1.85/1.29  Index Deletion       : 0.00
% 1.85/1.29  Index Matching       : 0.00
% 1.85/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
