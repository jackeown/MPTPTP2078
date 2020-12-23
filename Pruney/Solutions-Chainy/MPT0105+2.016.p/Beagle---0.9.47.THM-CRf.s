%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:49 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  34 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k2_xboole_0(A_32,B_33)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_123,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = A_40
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2384,plain,(
    ! [A_121,B_122] : k4_xboole_0(k4_xboole_0(A_121,B_122),B_122) = k4_xboole_0(A_121,B_122) ),
    inference(resolution,[status(thm)],[c_20,c_123])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2426,plain,(
    ! [A_121,B_122] : k4_xboole_0(k4_xboole_0(A_121,B_122),k4_xboole_0(A_121,B_122)) = k3_xboole_0(k4_xboole_0(A_121,B_122),B_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_2384,c_18])).

tff(c_2507,plain,(
    ! [B_122,A_121] : k3_xboole_0(B_122,k4_xboole_0(A_121,B_122)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2,c_2426])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_532,plain,(
    ! [A_59,B_60] : k4_xboole_0(k2_xboole_0(A_59,B_60),k3_xboole_0(A_59,B_60)) = k5_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5381,plain,(
    ! [A_192,B_193] : k4_xboole_0(k2_xboole_0(A_192,B_193),k3_xboole_0(B_193,A_192)) = k5_xboole_0(A_192,B_193) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_532])).

tff(c_5521,plain,(
    ! [A_6,B_7] : k4_xboole_0(k2_xboole_0(A_6,B_7),k3_xboole_0(k4_xboole_0(B_7,A_6),A_6)) = k5_xboole_0(A_6,k4_xboole_0(B_7,A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_5381])).

tff(c_5551,plain,(
    ! [A_6,B_7] : k5_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2507,c_2,c_5521])).

tff(c_30,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5551,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:56:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.88  
% 4.47/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.89  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.47/1.89  
% 4.47/1.89  %Foreground sorts:
% 4.47/1.89  
% 4.47/1.89  
% 4.47/1.89  %Background operators:
% 4.47/1.89  
% 4.47/1.89  
% 4.47/1.89  %Foreground operators:
% 4.47/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.47/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.47/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.47/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.47/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.47/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.47/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.47/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.47/1.89  
% 4.47/1.90  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.47/1.90  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.47/1.90  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.47/1.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.47/1.90  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.47/1.90  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.47/1.90  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.47/1.90  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.47/1.90  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 4.47/1.90  tff(f_56, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.47/1.90  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.47/1.90  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.47/1.90  tff(c_54, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k2_xboole_0(A_32, B_33))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.47/1.90  tff(c_64, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_54])).
% 4.47/1.90  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.47/1.90  tff(c_20, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.47/1.90  tff(c_123, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=A_40 | ~r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.47/1.90  tff(c_2384, plain, (![A_121, B_122]: (k4_xboole_0(k4_xboole_0(A_121, B_122), B_122)=k4_xboole_0(A_121, B_122))), inference(resolution, [status(thm)], [c_20, c_123])).
% 4.47/1.90  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.47/1.90  tff(c_2426, plain, (![A_121, B_122]: (k4_xboole_0(k4_xboole_0(A_121, B_122), k4_xboole_0(A_121, B_122))=k3_xboole_0(k4_xboole_0(A_121, B_122), B_122))), inference(superposition, [status(thm), theory('equality')], [c_2384, c_18])).
% 4.47/1.90  tff(c_2507, plain, (![B_122, A_121]: (k3_xboole_0(B_122, k4_xboole_0(A_121, B_122))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2, c_2426])).
% 4.47/1.90  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.47/1.90  tff(c_532, plain, (![A_59, B_60]: (k4_xboole_0(k2_xboole_0(A_59, B_60), k3_xboole_0(A_59, B_60))=k5_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.47/1.90  tff(c_5381, plain, (![A_192, B_193]: (k4_xboole_0(k2_xboole_0(A_192, B_193), k3_xboole_0(B_193, A_192))=k5_xboole_0(A_192, B_193))), inference(superposition, [status(thm), theory('equality')], [c_2, c_532])).
% 4.47/1.90  tff(c_5521, plain, (![A_6, B_7]: (k4_xboole_0(k2_xboole_0(A_6, B_7), k3_xboole_0(k4_xboole_0(B_7, A_6), A_6))=k5_xboole_0(A_6, k4_xboole_0(B_7, A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_5381])).
% 4.47/1.90  tff(c_5551, plain, (![A_6, B_7]: (k5_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2507, c_2, c_5521])).
% 4.47/1.90  tff(c_30, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.47/1.90  tff(c_5725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5551, c_30])).
% 4.47/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.90  
% 4.47/1.90  Inference rules
% 4.47/1.90  ----------------------
% 4.47/1.90  #Ref     : 0
% 4.47/1.90  #Sup     : 1432
% 4.47/1.90  #Fact    : 0
% 4.47/1.90  #Define  : 0
% 4.47/1.90  #Split   : 0
% 4.47/1.90  #Chain   : 0
% 4.47/1.90  #Close   : 0
% 4.47/1.90  
% 4.47/1.90  Ordering : KBO
% 4.47/1.90  
% 4.47/1.90  Simplification rules
% 4.47/1.90  ----------------------
% 4.47/1.90  #Subsume      : 0
% 4.47/1.90  #Demod        : 1321
% 4.47/1.90  #Tautology    : 1001
% 4.47/1.90  #SimpNegUnit  : 0
% 4.47/1.90  #BackRed      : 3
% 4.47/1.90  
% 4.47/1.90  #Partial instantiations: 0
% 4.47/1.90  #Strategies tried      : 1
% 4.47/1.90  
% 4.47/1.90  Timing (in seconds)
% 4.47/1.90  ----------------------
% 4.47/1.90  Preprocessing        : 0.28
% 4.47/1.90  Parsing              : 0.15
% 4.47/1.90  CNF conversion       : 0.02
% 4.47/1.90  Main loop            : 0.85
% 4.47/1.90  Inferencing          : 0.26
% 4.47/1.90  Reduction            : 0.38
% 4.47/1.90  Demodulation         : 0.31
% 4.47/1.90  BG Simplification    : 0.03
% 4.47/1.90  Subsumption          : 0.11
% 4.47/1.90  Abstraction          : 0.04
% 4.47/1.90  MUC search           : 0.00
% 4.47/1.90  Cooper               : 0.00
% 4.47/1.90  Total                : 1.16
% 4.47/1.90  Index Insertion      : 0.00
% 4.47/1.90  Index Deletion       : 0.00
% 4.47/1.90  Index Matching       : 0.00
% 4.47/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
