%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:59 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  36 expanded)
%              Number of equality atoms :   24 (  31 expanded)
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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_213,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_232,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_213])).

tff(c_260,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_232])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_174,plain,(
    ! [A_32,B_33] : k4_xboole_0(k2_xboole_0(A_32,B_33),B_33) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_187,plain,(
    ! [A_32] : k4_xboole_0(A_32,k1_xboole_0) = k2_xboole_0(A_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_10])).

tff(c_196,plain,(
    ! [A_32] : k2_xboole_0(A_32,k1_xboole_0) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_187])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_419,plain,(
    ! [A_46,B_47] : k2_xboole_0(k4_xboole_0(A_46,B_47),k4_xboole_0(B_47,A_46)) = k5_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_431,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(k4_xboole_0(A_12,B_13),A_12)) = k5_xboole_0(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_419])).

tff(c_887,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_71,c_431])).

tff(c_915,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_887])).

tff(c_941,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_915])).

tff(c_22,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.29  
% 2.36/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.29  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.36/1.29  
% 2.36/1.29  %Foreground sorts:
% 2.36/1.29  
% 2.36/1.29  
% 2.36/1.29  %Background operators:
% 2.36/1.29  
% 2.36/1.29  
% 2.36/1.29  %Foreground operators:
% 2.36/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.36/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.36/1.29  
% 2.36/1.30  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.36/1.30  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.36/1.30  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.36/1.30  tff(f_37, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.36/1.30  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.36/1.30  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.36/1.30  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.36/1.30  tff(f_48, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.36/1.30  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.36/1.30  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.36/1.30  tff(c_213, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.36/1.30  tff(c_232, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k3_xboole_0(A_12, k4_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_213])).
% 2.36/1.30  tff(c_260, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_232])).
% 2.36/1.30  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.30  tff(c_174, plain, (![A_32, B_33]: (k4_xboole_0(k2_xboole_0(A_32, B_33), B_33)=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.30  tff(c_187, plain, (![A_32]: (k4_xboole_0(A_32, k1_xboole_0)=k2_xboole_0(A_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_174, c_10])).
% 2.36/1.30  tff(c_196, plain, (![A_32]: (k2_xboole_0(A_32, k1_xboole_0)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_187])).
% 2.36/1.30  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.30  tff(c_59, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.30  tff(c_71, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_59])).
% 2.36/1.30  tff(c_419, plain, (![A_46, B_47]: (k2_xboole_0(k4_xboole_0(A_46, B_47), k4_xboole_0(B_47, A_46))=k5_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.36/1.30  tff(c_431, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(k4_xboole_0(A_12, B_13), A_12))=k5_xboole_0(A_12, k4_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_419])).
% 2.36/1.30  tff(c_887, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k4_xboole_0(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_71, c_431])).
% 2.36/1.30  tff(c_915, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k3_xboole_0(A_12, k4_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_887])).
% 2.36/1.30  tff(c_941, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_915])).
% 2.36/1.30  tff(c_22, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.36/1.30  tff(c_1057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_941, c_22])).
% 2.36/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.30  
% 2.36/1.30  Inference rules
% 2.36/1.30  ----------------------
% 2.36/1.30  #Ref     : 0
% 2.36/1.30  #Sup     : 251
% 2.36/1.30  #Fact    : 0
% 2.36/1.30  #Define  : 0
% 2.36/1.30  #Split   : 0
% 2.36/1.30  #Chain   : 0
% 2.36/1.30  #Close   : 0
% 2.36/1.30  
% 2.36/1.30  Ordering : KBO
% 2.36/1.30  
% 2.36/1.30  Simplification rules
% 2.36/1.30  ----------------------
% 2.36/1.30  #Subsume      : 0
% 2.36/1.30  #Demod        : 206
% 2.36/1.30  #Tautology    : 189
% 2.36/1.30  #SimpNegUnit  : 0
% 2.36/1.30  #BackRed      : 1
% 2.36/1.30  
% 2.36/1.30  #Partial instantiations: 0
% 2.36/1.30  #Strategies tried      : 1
% 2.36/1.30  
% 2.36/1.30  Timing (in seconds)
% 2.36/1.30  ----------------------
% 2.36/1.30  Preprocessing        : 0.25
% 2.36/1.30  Parsing              : 0.14
% 2.36/1.30  CNF conversion       : 0.01
% 2.36/1.30  Main loop            : 0.30
% 2.36/1.30  Inferencing          : 0.12
% 2.36/1.30  Reduction            : 0.11
% 2.36/1.30  Demodulation         : 0.08
% 2.36/1.30  BG Simplification    : 0.01
% 2.36/1.30  Subsumption          : 0.04
% 2.36/1.30  Abstraction          : 0.02
% 2.36/1.30  MUC search           : 0.00
% 2.36/1.30  Cooper               : 0.00
% 2.36/1.30  Total                : 0.58
% 2.36/1.30  Index Insertion      : 0.00
% 2.36/1.30  Index Deletion       : 0.00
% 2.36/1.30  Index Matching       : 0.00
% 2.36/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
