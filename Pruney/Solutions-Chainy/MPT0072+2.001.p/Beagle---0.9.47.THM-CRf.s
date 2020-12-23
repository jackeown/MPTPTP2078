%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:24 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   31 (  37 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  30 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1

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
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_138,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_xboole_0(A_19,B_20),B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_93,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = k2_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_8])).

tff(c_108,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_93])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_257,plain,(
    ! [B_27,A_28] : k4_xboole_0(k2_xboole_0(B_27,A_28),B_27) = k4_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86])).

tff(c_280,plain,(
    ! [A_19] : k4_xboole_0(k1_xboole_0,A_19) = k4_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_257])).

tff(c_300,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_14,c_280])).

tff(c_77,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k3_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ~ r1_xboole_0('#skF_1',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_16])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.62/1.14  
% 1.62/1.14  %Foreground sorts:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Background operators:
% 1.62/1.14  
% 1.62/1.14  
% 1.62/1.14  %Foreground operators:
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.62/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.62/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.14  
% 1.62/1.15  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.62/1.15  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.62/1.15  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.62/1.15  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.62/1.15  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.62/1.15  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.62/1.15  tff(f_42, negated_conjecture, ~(![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.62/1.15  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.15  tff(c_138, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.15  tff(c_160, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_138])).
% 1.62/1.15  tff(c_14, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.62/1.15  tff(c_86, plain, (![A_19, B_20]: (k4_xboole_0(k2_xboole_0(A_19, B_20), B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.15  tff(c_93, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=k2_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_86, c_8])).
% 1.62/1.15  tff(c_108, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_93])).
% 1.62/1.15  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.15  tff(c_257, plain, (![B_27, A_28]: (k4_xboole_0(k2_xboole_0(B_27, A_28), B_27)=k4_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_2, c_86])).
% 1.62/1.15  tff(c_280, plain, (![A_19]: (k4_xboole_0(k1_xboole_0, A_19)=k4_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_108, c_257])).
% 1.62/1.15  tff(c_300, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_160, c_14, c_280])).
% 1.62/1.15  tff(c_77, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k3_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.15  tff(c_16, plain, (~r1_xboole_0('#skF_1', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.15  tff(c_85, plain, (k3_xboole_0('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_77, c_16])).
% 1.62/1.15  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_300, c_85])).
% 1.62/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.15  
% 1.62/1.15  Inference rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Ref     : 0
% 1.62/1.15  #Sup     : 67
% 1.62/1.15  #Fact    : 0
% 1.62/1.15  #Define  : 0
% 1.62/1.15  #Split   : 0
% 1.62/1.15  #Chain   : 0
% 1.62/1.15  #Close   : 0
% 1.62/1.15  
% 1.62/1.15  Ordering : KBO
% 1.62/1.15  
% 1.62/1.15  Simplification rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Subsume      : 0
% 1.62/1.15  #Demod        : 36
% 1.62/1.15  #Tautology    : 53
% 1.62/1.15  #SimpNegUnit  : 0
% 1.62/1.15  #BackRed      : 2
% 1.62/1.15  
% 1.62/1.15  #Partial instantiations: 0
% 1.62/1.15  #Strategies tried      : 1
% 1.62/1.15  
% 1.62/1.15  Timing (in seconds)
% 1.62/1.15  ----------------------
% 1.62/1.15  Preprocessing        : 0.24
% 1.62/1.15  Parsing              : 0.13
% 1.62/1.15  CNF conversion       : 0.01
% 1.62/1.15  Main loop            : 0.15
% 1.62/1.15  Inferencing          : 0.06
% 1.62/1.15  Reduction            : 0.05
% 1.62/1.15  Demodulation         : 0.04
% 1.62/1.15  BG Simplification    : 0.01
% 1.62/1.15  Subsumption          : 0.02
% 1.62/1.15  Abstraction          : 0.01
% 1.62/1.15  MUC search           : 0.00
% 1.62/1.15  Cooper               : 0.00
% 1.62/1.15  Total                : 0.42
% 1.62/1.15  Index Insertion      : 0.00
% 1.62/1.15  Index Deletion       : 0.00
% 1.62/1.15  Index Matching       : 0.00
% 1.62/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
