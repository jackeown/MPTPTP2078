%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:15 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  25 expanded)
%              Number of equality atoms :   19 (  20 expanded)
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

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_70,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_22,B_23,C_24] : k4_xboole_0(k4_xboole_0(A_22,B_23),C_24) = k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2335,plain,(
    ! [A_82,B_83,C_84] : k4_xboole_0(k4_xboole_0(A_82,B_83),k4_xboole_0(A_82,k2_xboole_0(B_83,C_84))) = k3_xboole_0(k4_xboole_0(A_82,B_83),C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_14])).

tff(c_2513,plain,(
    ! [A_82,A_3] : k4_xboole_0(k4_xboole_0(A_82,A_3),k4_xboole_0(A_82,A_3)) = k3_xboole_0(k4_xboole_0(A_82,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2335])).

tff(c_2565,plain,(
    ! [A_82,A_3] : k3_xboole_0(k4_xboole_0(A_82,A_3),A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2513])).

tff(c_43,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k3_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_51,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43,c_16])).

tff(c_2569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2565,c_51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.57  
% 3.42/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.58  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.42/1.58  
% 3.42/1.58  %Foreground sorts:
% 3.42/1.58  
% 3.42/1.58  
% 3.42/1.58  %Background operators:
% 3.42/1.58  
% 3.42/1.58  
% 3.42/1.58  %Foreground operators:
% 3.42/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.42/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.42/1.58  
% 3.42/1.59  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.42/1.59  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.42/1.59  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.42/1.59  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.42/1.59  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.42/1.59  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.42/1.59  tff(f_42, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.42/1.59  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.42/1.59  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.42/1.59  tff(c_52, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.59  tff(c_67, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_52])).
% 3.42/1.59  tff(c_70, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_67])).
% 3.42/1.59  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.59  tff(c_92, plain, (![A_22, B_23, C_24]: (k4_xboole_0(k4_xboole_0(A_22, B_23), C_24)=k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.59  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.59  tff(c_2335, plain, (![A_82, B_83, C_84]: (k4_xboole_0(k4_xboole_0(A_82, B_83), k4_xboole_0(A_82, k2_xboole_0(B_83, C_84)))=k3_xboole_0(k4_xboole_0(A_82, B_83), C_84))), inference(superposition, [status(thm), theory('equality')], [c_92, c_14])).
% 3.42/1.59  tff(c_2513, plain, (![A_82, A_3]: (k4_xboole_0(k4_xboole_0(A_82, A_3), k4_xboole_0(A_82, A_3))=k3_xboole_0(k4_xboole_0(A_82, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2335])).
% 3.42/1.59  tff(c_2565, plain, (![A_82, A_3]: (k3_xboole_0(k4_xboole_0(A_82, A_3), A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2513])).
% 3.42/1.59  tff(c_43, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k3_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.59  tff(c_16, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.42/1.59  tff(c_51, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_43, c_16])).
% 3.42/1.59  tff(c_2569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2565, c_51])).
% 3.42/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.59  
% 3.42/1.59  Inference rules
% 3.42/1.59  ----------------------
% 3.42/1.59  #Ref     : 0
% 3.42/1.59  #Sup     : 605
% 3.42/1.59  #Fact    : 0
% 3.42/1.59  #Define  : 0
% 3.42/1.59  #Split   : 0
% 3.42/1.59  #Chain   : 0
% 3.42/1.59  #Close   : 0
% 3.42/1.59  
% 3.42/1.59  Ordering : KBO
% 3.42/1.59  
% 3.42/1.59  Simplification rules
% 3.42/1.59  ----------------------
% 3.42/1.59  #Subsume      : 0
% 3.42/1.59  #Demod        : 497
% 3.42/1.59  #Tautology    : 389
% 3.42/1.59  #SimpNegUnit  : 0
% 3.42/1.59  #BackRed      : 2
% 3.42/1.59  
% 3.42/1.59  #Partial instantiations: 0
% 3.42/1.59  #Strategies tried      : 1
% 3.42/1.59  
% 3.42/1.59  Timing (in seconds)
% 3.42/1.59  ----------------------
% 3.42/1.59  Preprocessing        : 0.26
% 3.42/1.59  Parsing              : 0.14
% 3.42/1.59  CNF conversion       : 0.01
% 3.42/1.59  Main loop            : 0.57
% 3.42/1.59  Inferencing          : 0.21
% 3.42/1.59  Reduction            : 0.21
% 3.42/1.59  Demodulation         : 0.17
% 3.42/1.59  BG Simplification    : 0.02
% 3.42/1.59  Subsumption          : 0.08
% 3.42/1.59  Abstraction          : 0.04
% 3.42/1.59  MUC search           : 0.00
% 3.42/1.59  Cooper               : 0.00
% 3.42/1.59  Total                : 0.85
% 3.42/1.59  Index Insertion      : 0.00
% 3.42/1.59  Index Deletion       : 0.00
% 3.42/1.59  Index Matching       : 0.00
% 3.42/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
