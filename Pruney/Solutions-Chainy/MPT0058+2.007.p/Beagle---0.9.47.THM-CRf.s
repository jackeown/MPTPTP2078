%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:03 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   32 (  42 expanded)
%              Number of equality atoms :   25 (  32 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_46])).

tff(c_84,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_84])).

tff(c_193,plain,(
    ! [A_32,B_33] : k2_xboole_0(A_32,k4_xboole_0(B_33,A_32)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_208,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = k2_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_193])).

tff(c_215,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_208])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_84])).

tff(c_202,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k2_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_193])).

tff(c_544,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_202])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_250,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_259,plain,(
    ! [A_35,B_36] : k2_xboole_0(k4_xboole_0(A_35,B_36),k3_xboole_0(A_35,B_36)) = k2_xboole_0(k4_xboole_0(A_35,B_36),A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_14])).

tff(c_293,plain,(
    ! [A_35,B_36] : k2_xboole_0(k4_xboole_0(A_35,B_36),k3_xboole_0(A_35,B_36)) = k2_xboole_0(A_35,k4_xboole_0(A_35,B_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_259])).

tff(c_728,plain,(
    ! [A_54,B_55] : k2_xboole_0(k4_xboole_0(A_54,B_55),k3_xboole_0(A_54,B_55)) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_293])).

tff(c_734,plain,(
    ! [A_54,B_55] : k2_xboole_0(k3_xboole_0(A_54,B_55),k4_xboole_0(A_54,B_55)) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_2])).

tff(c_20,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:47:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.25  
% 2.23/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.26  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.23/1.26  
% 2.23/1.26  %Foreground sorts:
% 2.23/1.26  
% 2.23/1.26  
% 2.23/1.26  %Background operators:
% 2.23/1.26  
% 2.23/1.26  
% 2.23/1.26  %Foreground operators:
% 2.23/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.26  
% 2.23/1.27  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.23/1.27  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.23/1.27  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.23/1.27  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.23/1.27  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.23/1.27  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.23/1.27  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.23/1.27  tff(f_46, negated_conjecture, ~(![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.23/1.27  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.27  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.23/1.27  tff(c_46, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.27  tff(c_49, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_46])).
% 2.23/1.27  tff(c_84, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.27  tff(c_91, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_49, c_84])).
% 2.23/1.27  tff(c_193, plain, (![A_32, B_33]: (k2_xboole_0(A_32, k4_xboole_0(B_33, A_32))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.23/1.27  tff(c_208, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=k2_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_91, c_193])).
% 2.23/1.27  tff(c_215, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_208])).
% 2.23/1.27  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.27  tff(c_92, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_84])).
% 2.23/1.27  tff(c_202, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k2_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_92, c_193])).
% 2.23/1.27  tff(c_544, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(A_8, B_9))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_215, c_202])).
% 2.23/1.27  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.27  tff(c_250, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.23/1.27  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.23/1.27  tff(c_259, plain, (![A_35, B_36]: (k2_xboole_0(k4_xboole_0(A_35, B_36), k3_xboole_0(A_35, B_36))=k2_xboole_0(k4_xboole_0(A_35, B_36), A_35))), inference(superposition, [status(thm), theory('equality')], [c_250, c_14])).
% 2.23/1.27  tff(c_293, plain, (![A_35, B_36]: (k2_xboole_0(k4_xboole_0(A_35, B_36), k3_xboole_0(A_35, B_36))=k2_xboole_0(A_35, k4_xboole_0(A_35, B_36)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_259])).
% 2.23/1.27  tff(c_728, plain, (![A_54, B_55]: (k2_xboole_0(k4_xboole_0(A_54, B_55), k3_xboole_0(A_54, B_55))=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_544, c_293])).
% 2.23/1.27  tff(c_734, plain, (![A_54, B_55]: (k2_xboole_0(k3_xboole_0(A_54, B_55), k4_xboole_0(A_54, B_55))=A_54)), inference(superposition, [status(thm), theory('equality')], [c_728, c_2])).
% 2.23/1.27  tff(c_20, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.23/1.27  tff(c_797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_734, c_20])).
% 2.23/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  
% 2.23/1.27  Inference rules
% 2.23/1.27  ----------------------
% 2.23/1.27  #Ref     : 0
% 2.23/1.27  #Sup     : 183
% 2.23/1.27  #Fact    : 0
% 2.23/1.27  #Define  : 0
% 2.23/1.27  #Split   : 0
% 2.23/1.27  #Chain   : 0
% 2.23/1.27  #Close   : 0
% 2.23/1.27  
% 2.23/1.27  Ordering : KBO
% 2.23/1.27  
% 2.23/1.27  Simplification rules
% 2.23/1.27  ----------------------
% 2.23/1.27  #Subsume      : 0
% 2.23/1.27  #Demod        : 139
% 2.23/1.27  #Tautology    : 157
% 2.23/1.27  #SimpNegUnit  : 0
% 2.23/1.27  #BackRed      : 1
% 2.23/1.27  
% 2.23/1.27  #Partial instantiations: 0
% 2.23/1.27  #Strategies tried      : 1
% 2.23/1.27  
% 2.23/1.27  Timing (in seconds)
% 2.23/1.27  ----------------------
% 2.23/1.27  Preprocessing        : 0.26
% 2.23/1.27  Parsing              : 0.15
% 2.23/1.27  CNF conversion       : 0.01
% 2.23/1.27  Main loop            : 0.26
% 2.23/1.27  Inferencing          : 0.10
% 2.23/1.27  Reduction            : 0.10
% 2.23/1.27  Demodulation         : 0.08
% 2.23/1.27  BG Simplification    : 0.01
% 2.23/1.27  Subsumption          : 0.04
% 2.23/1.27  Abstraction          : 0.01
% 2.23/1.27  MUC search           : 0.00
% 2.23/1.27  Cooper               : 0.00
% 2.23/1.27  Total                : 0.55
% 2.23/1.27  Index Insertion      : 0.00
% 2.23/1.27  Index Deletion       : 0.00
% 2.23/1.27  Index Matching       : 0.00
% 2.23/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
