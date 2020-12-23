%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:03 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  28 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_112])).

tff(c_198,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_217,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_198])).

tff(c_227,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_217])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_261,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_270,plain,(
    ! [A_31,B_32] : k2_xboole_0(k4_xboole_0(A_31,B_32),k3_xboole_0(A_31,B_32)) = k2_xboole_0(k4_xboole_0(A_31,B_32),A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_12])).

tff(c_305,plain,(
    ! [A_31,B_32] : k2_xboole_0(k4_xboole_0(A_31,B_32),k3_xboole_0(A_31,B_32)) = k2_xboole_0(A_31,k4_xboole_0(A_31,B_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_270])).

tff(c_907,plain,(
    ! [A_57,B_58] : k2_xboole_0(k4_xboole_0(A_57,B_58),k3_xboole_0(A_57,B_58)) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_305])).

tff(c_913,plain,(
    ! [A_57,B_58] : k2_xboole_0(k3_xboole_0(A_57,B_58),k4_xboole_0(A_57,B_58)) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_2])).

tff(c_16,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.80  
% 2.80/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.81  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.80/1.81  
% 2.80/1.81  %Foreground sorts:
% 2.80/1.81  
% 2.80/1.81  
% 2.80/1.81  %Background operators:
% 2.80/1.81  
% 2.80/1.81  
% 2.80/1.81  %Foreground operators:
% 2.80/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.81  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.81  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.80/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.80/1.81  
% 3.07/1.82  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.07/1.82  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.07/1.82  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.07/1.82  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.07/1.82  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.07/1.82  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.07/1.82  tff(f_42, negated_conjecture, ~(![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.07/1.82  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.07/1.82  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.07/1.82  tff(c_112, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.82  tff(c_116, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_112])).
% 3.07/1.82  tff(c_198, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.07/1.82  tff(c_217, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_116, c_198])).
% 3.07/1.82  tff(c_227, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(A_6, B_7))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_217])).
% 3.07/1.82  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.82  tff(c_261, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.07/1.82  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.07/1.82  tff(c_270, plain, (![A_31, B_32]: (k2_xboole_0(k4_xboole_0(A_31, B_32), k3_xboole_0(A_31, B_32))=k2_xboole_0(k4_xboole_0(A_31, B_32), A_31))), inference(superposition, [status(thm), theory('equality')], [c_261, c_12])).
% 3.07/1.82  tff(c_305, plain, (![A_31, B_32]: (k2_xboole_0(k4_xboole_0(A_31, B_32), k3_xboole_0(A_31, B_32))=k2_xboole_0(A_31, k4_xboole_0(A_31, B_32)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_270])).
% 3.07/1.82  tff(c_907, plain, (![A_57, B_58]: (k2_xboole_0(k4_xboole_0(A_57, B_58), k3_xboole_0(A_57, B_58))=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_227, c_305])).
% 3.07/1.82  tff(c_913, plain, (![A_57, B_58]: (k2_xboole_0(k3_xboole_0(A_57, B_58), k4_xboole_0(A_57, B_58))=A_57)), inference(superposition, [status(thm), theory('equality')], [c_907, c_2])).
% 3.07/1.82  tff(c_16, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.07/1.82  tff(c_979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_913, c_16])).
% 3.07/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.82  
% 3.07/1.82  Inference rules
% 3.07/1.82  ----------------------
% 3.07/1.82  #Ref     : 0
% 3.07/1.82  #Sup     : 232
% 3.07/1.82  #Fact    : 0
% 3.07/1.82  #Define  : 0
% 3.07/1.82  #Split   : 0
% 3.07/1.82  #Chain   : 0
% 3.07/1.82  #Close   : 0
% 3.07/1.82  
% 3.07/1.82  Ordering : KBO
% 3.07/1.82  
% 3.07/1.82  Simplification rules
% 3.07/1.82  ----------------------
% 3.07/1.82  #Subsume      : 0
% 3.07/1.82  #Demod        : 197
% 3.07/1.82  #Tautology    : 194
% 3.07/1.82  #SimpNegUnit  : 0
% 3.07/1.82  #BackRed      : 1
% 3.07/1.82  
% 3.07/1.82  #Partial instantiations: 0
% 3.07/1.82  #Strategies tried      : 1
% 3.07/1.82  
% 3.07/1.82  Timing (in seconds)
% 3.07/1.82  ----------------------
% 3.07/1.83  Preprocessing        : 0.41
% 3.07/1.83  Parsing              : 0.23
% 3.07/1.83  CNF conversion       : 0.03
% 3.07/1.83  Main loop            : 0.49
% 3.07/1.83  Inferencing          : 0.18
% 3.07/1.83  Reduction            : 0.19
% 3.07/1.83  Demodulation         : 0.16
% 3.07/1.83  BG Simplification    : 0.02
% 3.07/1.83  Subsumption          : 0.06
% 3.07/1.83  Abstraction          : 0.03
% 3.07/1.83  MUC search           : 0.00
% 3.07/1.83  Cooper               : 0.00
% 3.07/1.83  Total                : 0.94
% 3.07/1.83  Index Insertion      : 0.00
% 3.07/1.83  Index Deletion       : 0.00
% 3.07/1.83  Index Matching       : 0.00
% 3.07/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
