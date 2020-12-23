%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:06 EST 2020

% Result     : Theorem 11.30s
% Output     : CNFRefutation 11.30s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  29 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_23,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_8,c_23])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_55,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k3_xboole_0(A_15,B_16),C_17) = k3_xboole_0(A_15,k4_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_256,plain,(
    ! [A_42,B_43,C_44] : k4_xboole_0(k4_xboole_0(A_42,B_43),C_44) = k4_xboole_0(A_42,k2_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_305,plain,(
    ! [A_13,B_14,C_44] : k4_xboole_0(A_13,k2_xboole_0(k4_xboole_0(A_13,B_14),C_44)) = k4_xboole_0(k3_xboole_0(A_13,B_14),C_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_256])).

tff(c_7714,plain,(
    ! [A_171,B_172,C_173] : k4_xboole_0(A_171,k2_xboole_0(k4_xboole_0(A_171,B_172),C_173)) = k3_xboole_0(A_171,k4_xboole_0(B_172,C_173)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_305])).

tff(c_7981,plain,(
    ! [A_6,B_7,C_173] : k4_xboole_0(k4_xboole_0(A_6,B_7),k2_xboole_0(k1_xboole_0,C_173)) = k3_xboole_0(k4_xboole_0(A_6,B_7),k4_xboole_0(A_6,C_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_7714])).

tff(c_8049,plain,(
    ! [A_6,B_7,C_173] : k3_xboole_0(k4_xboole_0(A_6,B_7),k4_xboole_0(A_6,C_173)) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_173)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_31,c_7981])).

tff(c_20,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_37109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8049,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.30/4.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.30/4.68  
% 11.30/4.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.30/4.69  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.30/4.69  
% 11.30/4.69  %Foreground sorts:
% 11.30/4.69  
% 11.30/4.69  
% 11.30/4.69  %Background operators:
% 11.30/4.69  
% 11.30/4.69  
% 11.30/4.69  %Foreground operators:
% 11.30/4.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.30/4.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.30/4.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.30/4.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.30/4.69  tff('#skF_2', type, '#skF_2': $i).
% 11.30/4.69  tff('#skF_3', type, '#skF_3': $i).
% 11.30/4.69  tff('#skF_1', type, '#skF_1': $i).
% 11.30/4.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.30/4.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.30/4.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.30/4.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.30/4.69  
% 11.30/4.69  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.30/4.69  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.30/4.69  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.30/4.69  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.30/4.69  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.30/4.69  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 11.30/4.69  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.30/4.69  tff(f_48, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 11.30/4.69  tff(c_14, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.30/4.69  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.30/4.69  tff(c_23, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.30/4.69  tff(c_31, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(resolution, [status(thm)], [c_8, c_23])).
% 11.30/4.69  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.30/4.69  tff(c_55, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.30/4.69  tff(c_66, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_55])).
% 11.30/4.69  tff(c_18, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k3_xboole_0(A_15, B_16), C_17)=k3_xboole_0(A_15, k4_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.30/4.69  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.30/4.69  tff(c_256, plain, (![A_42, B_43, C_44]: (k4_xboole_0(k4_xboole_0(A_42, B_43), C_44)=k4_xboole_0(A_42, k2_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.30/4.69  tff(c_305, plain, (![A_13, B_14, C_44]: (k4_xboole_0(A_13, k2_xboole_0(k4_xboole_0(A_13, B_14), C_44))=k4_xboole_0(k3_xboole_0(A_13, B_14), C_44))), inference(superposition, [status(thm), theory('equality')], [c_16, c_256])).
% 11.30/4.69  tff(c_7714, plain, (![A_171, B_172, C_173]: (k4_xboole_0(A_171, k2_xboole_0(k4_xboole_0(A_171, B_172), C_173))=k3_xboole_0(A_171, k4_xboole_0(B_172, C_173)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_305])).
% 11.30/4.69  tff(c_7981, plain, (![A_6, B_7, C_173]: (k4_xboole_0(k4_xboole_0(A_6, B_7), k2_xboole_0(k1_xboole_0, C_173))=k3_xboole_0(k4_xboole_0(A_6, B_7), k4_xboole_0(A_6, C_173)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_7714])).
% 11.30/4.69  tff(c_8049, plain, (![A_6, B_7, C_173]: (k3_xboole_0(k4_xboole_0(A_6, B_7), k4_xboole_0(A_6, C_173))=k4_xboole_0(A_6, k2_xboole_0(B_7, C_173)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_31, c_7981])).
% 11.30/4.69  tff(c_20, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.30/4.69  tff(c_37109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8049, c_20])).
% 11.30/4.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.30/4.69  
% 11.30/4.69  Inference rules
% 11.30/4.69  ----------------------
% 11.30/4.69  #Ref     : 1
% 11.30/4.69  #Sup     : 9333
% 11.30/4.69  #Fact    : 0
% 11.30/4.69  #Define  : 0
% 11.30/4.69  #Split   : 4
% 11.30/4.69  #Chain   : 0
% 11.30/4.69  #Close   : 0
% 11.30/4.69  
% 11.30/4.69  Ordering : KBO
% 11.30/4.69  
% 11.30/4.69  Simplification rules
% 11.30/4.69  ----------------------
% 11.30/4.69  #Subsume      : 360
% 11.30/4.69  #Demod        : 9225
% 11.30/4.69  #Tautology    : 6633
% 11.30/4.69  #SimpNegUnit  : 0
% 11.30/4.69  #BackRed      : 3
% 11.30/4.70  
% 11.30/4.70  #Partial instantiations: 0
% 11.30/4.70  #Strategies tried      : 1
% 11.30/4.70  
% 11.30/4.70  Timing (in seconds)
% 11.30/4.70  ----------------------
% 11.30/4.70  Preprocessing        : 0.39
% 11.30/4.70  Parsing              : 0.24
% 11.30/4.70  CNF conversion       : 0.02
% 11.30/4.70  Main loop            : 3.47
% 11.30/4.70  Inferencing          : 0.76
% 11.30/4.70  Reduction            : 1.90
% 11.30/4.70  Demodulation         : 1.67
% 11.30/4.70  BG Simplification    : 0.09
% 11.30/4.70  Subsumption          : 0.53
% 11.30/4.70  Abstraction          : 0.18
% 11.30/4.70  MUC search           : 0.00
% 11.30/4.70  Cooper               : 0.00
% 11.30/4.70  Total                : 3.89
% 11.30/4.70  Index Insertion      : 0.00
% 11.30/4.70  Index Deletion       : 0.00
% 11.30/4.70  Index Matching       : 0.00
% 11.30/4.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
