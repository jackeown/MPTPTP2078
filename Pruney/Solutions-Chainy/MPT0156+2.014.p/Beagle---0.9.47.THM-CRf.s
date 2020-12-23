%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:16 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :   37 (  48 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :   24 (  35 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_xboole_0(k1_tarski(A_6),k1_enumset1(B_7,C_8,D_9)) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_119,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k1_tarski(A_35),k2_xboole_0(k1_tarski(B_36),C_37)) = k2_xboole_0(k2_tarski(A_35,B_36),C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_168,plain,(
    ! [A_43,A_44,B_45] : k2_xboole_0(k2_tarski(A_43,A_44),k1_tarski(B_45)) = k2_xboole_0(k1_tarski(A_43),k2_tarski(A_44,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_119])).

tff(c_180,plain,(
    ! [A_15,B_45] : k2_xboole_0(k1_tarski(A_15),k2_tarski(A_15,B_45)) = k2_xboole_0(k1_tarski(A_15),k1_tarski(B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_168])).

tff(c_185,plain,(
    ! [A_46,B_47] : k2_xboole_0(k1_tarski(A_46),k2_tarski(A_46,B_47)) = k2_tarski(A_46,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_180])).

tff(c_207,plain,(
    ! [A_15] : k2_xboole_0(k1_tarski(A_15),k1_tarski(A_15)) = k2_tarski(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_185])).

tff(c_211,plain,(
    ! [A_48] : k2_xboole_0(k1_tarski(A_48),k1_tarski(A_48)) = k1_tarski(A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_207])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_312,plain,(
    ! [A_58,C_59] : k2_xboole_0(k1_tarski(A_58),k2_xboole_0(k1_tarski(A_58),C_59)) = k2_xboole_0(k1_tarski(A_58),C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_2])).

tff(c_358,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_xboole_0(k1_tarski(A_6),k2_enumset1(A_6,B_7,C_8,D_9)) = k2_xboole_0(k1_tarski(A_6),k1_enumset1(B_7,C_8,D_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_312])).

tff(c_2891,plain,(
    ! [A_144,B_145,C_146,D_147] : k2_xboole_0(k1_tarski(A_144),k2_enumset1(A_144,B_145,C_146,D_147)) = k2_enumset1(A_144,B_145,C_146,D_147) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_358])).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k2_xboole_0(k1_tarski(A_10),k2_enumset1(B_11,C_12,D_13,E_14)) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2914,plain,(
    ! [A_144,B_145,C_146,D_147] : k3_enumset1(A_144,A_144,B_145,C_146,D_147) = k2_enumset1(A_144,B_145,C_146,D_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_2891,c_8])).

tff(c_14,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2914,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.38/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.87  
% 4.38/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.87  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.38/1.87  
% 4.38/1.87  %Foreground sorts:
% 4.38/1.87  
% 4.38/1.87  
% 4.38/1.87  %Background operators:
% 4.38/1.87  
% 4.38/1.87  
% 4.38/1.87  %Foreground operators:
% 4.38/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.38/1.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.38/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.38/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.38/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.38/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.38/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.38/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.38/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.38/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.38/1.87  
% 4.38/1.88  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 4.38/1.88  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.38/1.88  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 4.38/1.88  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.38/1.88  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 4.38/1.88  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.38/1.88  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k2_xboole_0(k1_tarski(A_6), k1_enumset1(B_7, C_8, D_9))=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.38/1.88  tff(c_10, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.38/1.88  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.38/1.88  tff(c_42, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.38/1.88  tff(c_119, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k1_tarski(A_35), k2_xboole_0(k1_tarski(B_36), C_37))=k2_xboole_0(k2_tarski(A_35, B_36), C_37))), inference(superposition, [status(thm), theory('equality')], [c_4, c_42])).
% 4.38/1.88  tff(c_168, plain, (![A_43, A_44, B_45]: (k2_xboole_0(k2_tarski(A_43, A_44), k1_tarski(B_45))=k2_xboole_0(k1_tarski(A_43), k2_tarski(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_119])).
% 4.38/1.88  tff(c_180, plain, (![A_15, B_45]: (k2_xboole_0(k1_tarski(A_15), k2_tarski(A_15, B_45))=k2_xboole_0(k1_tarski(A_15), k1_tarski(B_45)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_168])).
% 4.38/1.88  tff(c_185, plain, (![A_46, B_47]: (k2_xboole_0(k1_tarski(A_46), k2_tarski(A_46, B_47))=k2_tarski(A_46, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_180])).
% 4.38/1.88  tff(c_207, plain, (![A_15]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(A_15))=k2_tarski(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_10, c_185])).
% 4.38/1.88  tff(c_211, plain, (![A_48]: (k2_xboole_0(k1_tarski(A_48), k1_tarski(A_48))=k1_tarski(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_207])).
% 4.38/1.88  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.38/1.88  tff(c_312, plain, (![A_58, C_59]: (k2_xboole_0(k1_tarski(A_58), k2_xboole_0(k1_tarski(A_58), C_59))=k2_xboole_0(k1_tarski(A_58), C_59))), inference(superposition, [status(thm), theory('equality')], [c_211, c_2])).
% 4.38/1.88  tff(c_358, plain, (![A_6, B_7, C_8, D_9]: (k2_xboole_0(k1_tarski(A_6), k2_enumset1(A_6, B_7, C_8, D_9))=k2_xboole_0(k1_tarski(A_6), k1_enumset1(B_7, C_8, D_9)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_312])).
% 4.38/1.88  tff(c_2891, plain, (![A_144, B_145, C_146, D_147]: (k2_xboole_0(k1_tarski(A_144), k2_enumset1(A_144, B_145, C_146, D_147))=k2_enumset1(A_144, B_145, C_146, D_147))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_358])).
% 4.38/1.88  tff(c_8, plain, (![B_11, A_10, C_12, E_14, D_13]: (k2_xboole_0(k1_tarski(A_10), k2_enumset1(B_11, C_12, D_13, E_14))=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.38/1.88  tff(c_2914, plain, (![A_144, B_145, C_146, D_147]: (k3_enumset1(A_144, A_144, B_145, C_146, D_147)=k2_enumset1(A_144, B_145, C_146, D_147))), inference(superposition, [status(thm), theory('equality')], [c_2891, c_8])).
% 4.38/1.88  tff(c_14, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.38/1.88  tff(c_2967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2914, c_14])).
% 4.38/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.88  
% 4.38/1.88  Inference rules
% 4.38/1.88  ----------------------
% 4.38/1.88  #Ref     : 0
% 4.38/1.88  #Sup     : 714
% 4.38/1.88  #Fact    : 0
% 4.38/1.88  #Define  : 0
% 4.38/1.88  #Split   : 0
% 4.38/1.88  #Chain   : 0
% 4.38/1.88  #Close   : 0
% 4.38/1.88  
% 4.38/1.88  Ordering : KBO
% 4.38/1.88  
% 4.38/1.88  Simplification rules
% 4.38/1.88  ----------------------
% 4.38/1.88  #Subsume      : 95
% 4.38/1.88  #Demod        : 845
% 4.38/1.88  #Tautology    : 469
% 4.38/1.88  #SimpNegUnit  : 0
% 4.38/1.88  #BackRed      : 1
% 4.38/1.88  
% 4.38/1.88  #Partial instantiations: 0
% 4.38/1.88  #Strategies tried      : 1
% 4.38/1.88  
% 4.38/1.88  Timing (in seconds)
% 4.38/1.88  ----------------------
% 4.38/1.88  Preprocessing        : 0.30
% 4.38/1.88  Parsing              : 0.15
% 4.38/1.88  CNF conversion       : 0.02
% 4.38/1.88  Main loop            : 0.74
% 4.38/1.88  Inferencing          : 0.27
% 4.38/1.88  Reduction            : 0.33
% 4.38/1.88  Demodulation         : 0.29
% 4.38/1.88  BG Simplification    : 0.03
% 4.38/1.89  Subsumption          : 0.08
% 4.38/1.89  Abstraction          : 0.05
% 4.38/1.89  MUC search           : 0.00
% 4.38/1.89  Cooper               : 0.00
% 4.38/1.89  Total                : 1.07
% 4.38/1.89  Index Insertion      : 0.00
% 4.38/1.89  Index Deletion       : 0.00
% 4.38/1.89  Index Matching       : 0.00
% 4.38/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
