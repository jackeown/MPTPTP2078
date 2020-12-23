%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:56 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  31 expanded)
%              Number of equality atoms :   23 (  30 expanded)
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

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_61])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_130,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,k3_xboole_0(A_26,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_14])).

tff(c_524,plain,(
    ! [A_42,B_43] : k3_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_136])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_151,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_130])).

tff(c_533,plain,(
    ! [A_42,B_43] : k4_xboole_0(k3_xboole_0(A_42,B_43),k3_xboole_0(A_42,B_43)) = k4_xboole_0(k3_xboole_0(A_42,B_43),A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_151])).

tff(c_571,plain,(
    ! [A_42,B_43] : k4_xboole_0(k3_xboole_0(A_42,B_43),A_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_533])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_681,plain,(
    ! [A_47,B_48] : k2_xboole_0(k4_xboole_0(A_47,B_48),k4_xboole_0(B_48,A_47)) = k5_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_734,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),k4_xboole_0(k3_xboole_0(A_11,B_12),A_11)) = k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_681])).

tff(c_772,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_571,c_734])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:13:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.39  
% 2.58/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.39  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.58/1.39  
% 2.58/1.39  %Foreground sorts:
% 2.58/1.39  
% 2.58/1.39  
% 2.58/1.39  %Background operators:
% 2.58/1.39  
% 2.58/1.39  
% 2.58/1.39  %Foreground operators:
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.39  
% 2.84/1.40  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.84/1.40  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.84/1.40  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.84/1.40  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.84/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.84/1.40  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.84/1.40  tff(f_44, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.84/1.40  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.40  tff(c_61, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.40  tff(c_68, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_61])).
% 2.84/1.40  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.84/1.40  tff(c_130, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.40  tff(c_136, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, k3_xboole_0(A_26, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_14])).
% 2.84/1.40  tff(c_524, plain, (![A_42, B_43]: (k3_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_136])).
% 2.84/1.40  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.40  tff(c_151, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_130])).
% 2.84/1.40  tff(c_533, plain, (![A_42, B_43]: (k4_xboole_0(k3_xboole_0(A_42, B_43), k3_xboole_0(A_42, B_43))=k4_xboole_0(k3_xboole_0(A_42, B_43), A_42))), inference(superposition, [status(thm), theory('equality')], [c_524, c_151])).
% 2.84/1.40  tff(c_571, plain, (![A_42, B_43]: (k4_xboole_0(k3_xboole_0(A_42, B_43), A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_533])).
% 2.84/1.40  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.40  tff(c_681, plain, (![A_47, B_48]: (k2_xboole_0(k4_xboole_0(A_47, B_48), k4_xboole_0(B_48, A_47))=k5_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.84/1.40  tff(c_734, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), k4_xboole_0(k3_xboole_0(A_11, B_12), A_11))=k5_xboole_0(A_11, k3_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_681])).
% 2.84/1.40  tff(c_772, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_571, c_734])).
% 2.84/1.40  tff(c_18, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.40  tff(c_1535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_772, c_18])).
% 2.84/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.40  
% 2.84/1.40  Inference rules
% 2.84/1.40  ----------------------
% 2.84/1.40  #Ref     : 0
% 2.84/1.40  #Sup     : 369
% 2.84/1.40  #Fact    : 0
% 2.84/1.40  #Define  : 0
% 2.84/1.40  #Split   : 0
% 2.84/1.40  #Chain   : 0
% 2.84/1.40  #Close   : 0
% 2.84/1.40  
% 2.84/1.40  Ordering : KBO
% 2.84/1.40  
% 2.84/1.40  Simplification rules
% 2.84/1.40  ----------------------
% 2.84/1.40  #Subsume      : 4
% 2.84/1.40  #Demod        : 277
% 2.84/1.40  #Tautology    : 255
% 2.84/1.40  #SimpNegUnit  : 0
% 2.84/1.40  #BackRed      : 4
% 2.84/1.40  
% 2.84/1.40  #Partial instantiations: 0
% 2.84/1.40  #Strategies tried      : 1
% 2.84/1.40  
% 2.84/1.40  Timing (in seconds)
% 2.84/1.40  ----------------------
% 2.84/1.40  Preprocessing        : 0.26
% 2.84/1.40  Parsing              : 0.15
% 2.84/1.40  CNF conversion       : 0.01
% 2.84/1.40  Main loop            : 0.38
% 2.84/1.40  Inferencing          : 0.13
% 2.84/1.40  Reduction            : 0.16
% 2.84/1.40  Demodulation         : 0.13
% 2.84/1.40  BG Simplification    : 0.02
% 2.84/1.40  Subsumption          : 0.05
% 2.84/1.40  Abstraction          : 0.02
% 2.84/1.40  MUC search           : 0.00
% 2.84/1.40  Cooper               : 0.00
% 2.84/1.40  Total                : 0.67
% 2.84/1.40  Index Insertion      : 0.00
% 2.84/1.40  Index Deletion       : 0.00
% 2.84/1.40  Index Matching       : 0.00
% 2.84/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
