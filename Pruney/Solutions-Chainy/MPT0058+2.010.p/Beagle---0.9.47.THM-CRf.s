%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:03 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  24 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_17,B_18] : k2_xboole_0(k4_xboole_0(A_17,B_18),A_17) = A_17 ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_150,plain,(
    ! [A_29,B_30] : k2_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_163,plain,(
    ! [A_9,B_10] : k2_xboole_0(k4_xboole_0(A_9,B_10),k3_xboole_0(A_9,B_10)) = k2_xboole_0(k4_xboole_0(A_9,B_10),A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_150])).

tff(c_184,plain,(
    ! [A_32,B_33] : k2_xboole_0(k4_xboole_0(A_32,B_33),k3_xboole_0(A_32,B_33)) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2,c_163])).

tff(c_190,plain,(
    ! [A_32,B_33] : k2_xboole_0(k3_xboole_0(A_32,B_33),k4_xboole_0(A_32,B_33)) = A_32 ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_2])).

tff(c_12,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.16  
% 1.81/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.17  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.81/1.17  
% 1.81/1.17  %Foreground sorts:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Background operators:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Foreground operators:
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.81/1.17  
% 1.81/1.17  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.81/1.17  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.81/1.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.81/1.17  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.81/1.17  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.81/1.17  tff(f_40, negated_conjecture, ~(![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.81/1.17  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.17  tff(c_47, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.17  tff(c_52, plain, (![A_17, B_18]: (k2_xboole_0(k4_xboole_0(A_17, B_18), A_17)=A_17)), inference(resolution, [status(thm)], [c_6, c_47])).
% 1.81/1.17  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.81/1.17  tff(c_58, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(A_17, B_18))=A_17)), inference(superposition, [status(thm), theory('equality')], [c_52, c_2])).
% 1.81/1.17  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.81/1.17  tff(c_150, plain, (![A_29, B_30]: (k2_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.17  tff(c_163, plain, (![A_9, B_10]: (k2_xboole_0(k4_xboole_0(A_9, B_10), k3_xboole_0(A_9, B_10))=k2_xboole_0(k4_xboole_0(A_9, B_10), A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_150])).
% 1.81/1.17  tff(c_184, plain, (![A_32, B_33]: (k2_xboole_0(k4_xboole_0(A_32, B_33), k3_xboole_0(A_32, B_33))=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2, c_163])).
% 1.81/1.17  tff(c_190, plain, (![A_32, B_33]: (k2_xboole_0(k3_xboole_0(A_32, B_33), k4_xboole_0(A_32, B_33))=A_32)), inference(superposition, [status(thm), theory('equality')], [c_184, c_2])).
% 1.81/1.17  tff(c_12, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.81/1.17  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_190, c_12])).
% 1.81/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.17  
% 1.81/1.17  Inference rules
% 1.81/1.17  ----------------------
% 1.81/1.17  #Ref     : 0
% 1.81/1.17  #Sup     : 47
% 1.81/1.17  #Fact    : 0
% 1.81/1.17  #Define  : 0
% 1.81/1.17  #Split   : 0
% 1.81/1.17  #Chain   : 0
% 1.81/1.17  #Close   : 0
% 1.81/1.17  
% 1.81/1.17  Ordering : KBO
% 1.81/1.17  
% 1.81/1.17  Simplification rules
% 1.81/1.17  ----------------------
% 1.81/1.17  #Subsume      : 0
% 1.81/1.17  #Demod        : 12
% 1.81/1.17  #Tautology    : 33
% 1.81/1.17  #SimpNegUnit  : 0
% 1.81/1.17  #BackRed      : 1
% 1.81/1.17  
% 1.81/1.17  #Partial instantiations: 0
% 1.81/1.17  #Strategies tried      : 1
% 1.81/1.17  
% 1.81/1.17  Timing (in seconds)
% 1.81/1.17  ----------------------
% 1.81/1.18  Preprocessing        : 0.25
% 1.81/1.18  Parsing              : 0.14
% 1.81/1.18  CNF conversion       : 0.01
% 1.81/1.18  Main loop            : 0.16
% 1.81/1.18  Inferencing          : 0.06
% 1.81/1.18  Reduction            : 0.06
% 1.81/1.18  Demodulation         : 0.05
% 1.81/1.18  BG Simplification    : 0.01
% 1.81/1.18  Subsumption          : 0.03
% 1.81/1.18  Abstraction          : 0.01
% 1.81/1.18  MUC search           : 0.00
% 1.81/1.18  Cooper               : 0.00
% 1.81/1.18  Total                : 0.44
% 1.81/1.18  Index Insertion      : 0.00
% 1.81/1.18  Index Deletion       : 0.00
% 1.81/1.18  Index Matching       : 0.00
% 1.81/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
