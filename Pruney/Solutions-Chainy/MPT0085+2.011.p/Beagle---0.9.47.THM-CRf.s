%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:12 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  38 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_208,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,k3_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_988,plain,(
    ! [A_59,B_60] :
      ( ~ r1_xboole_0(A_59,B_60)
      | k3_xboole_0(A_59,B_60) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_208])).

tff(c_997,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_988])).

tff(c_18,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1007,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_18])).

tff(c_33,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_49,plain,(
    ! [A_23] : k2_xboole_0(k1_xboole_0,A_23) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_10])).

tff(c_1018,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1007,c_49])).

tff(c_1044,plain,(
    ! [A_61,B_62,C_63] : k4_xboole_0(k4_xboole_0(A_61,B_62),C_63) = k4_xboole_0(A_61,k2_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1165,plain,(
    ! [C_64] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_64)) = k4_xboole_0('#skF_3',C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_1018,c_1044])).

tff(c_1174,plain,(
    ! [C_64] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',C_64)) = k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_16])).

tff(c_1210,plain,(
    ! [C_64] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_64)) = k3_xboole_0('#skF_3',C_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1174])).

tff(c_20,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.47  
% 3.13/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.48  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.13/1.48  
% 3.13/1.48  %Foreground sorts:
% 3.13/1.48  
% 3.13/1.48  
% 3.13/1.48  %Background operators:
% 3.13/1.48  
% 3.13/1.48  
% 3.13/1.48  %Foreground operators:
% 3.13/1.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.13/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.13/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.13/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.13/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.48  
% 3.23/1.49  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.23/1.49  tff(f_64, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 3.23/1.49  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.23/1.49  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.23/1.49  tff(f_59, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.23/1.49  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.23/1.49  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.23/1.49  tff(f_55, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.23/1.49  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.23/1.49  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.23/1.49  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.23/1.49  tff(c_208, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, k3_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.49  tff(c_988, plain, (![A_59, B_60]: (~r1_xboole_0(A_59, B_60) | k3_xboole_0(A_59, B_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_208])).
% 3.23/1.49  tff(c_997, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_988])).
% 3.23/1.49  tff(c_18, plain, (![A_18, B_19]: (k2_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.23/1.49  tff(c_1007, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_997, c_18])).
% 3.23/1.49  tff(c_33, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.49  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.23/1.49  tff(c_49, plain, (![A_23]: (k2_xboole_0(k1_xboole_0, A_23)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_33, c_10])).
% 3.23/1.49  tff(c_1018, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1007, c_49])).
% 3.23/1.49  tff(c_1044, plain, (![A_61, B_62, C_63]: (k4_xboole_0(k4_xboole_0(A_61, B_62), C_63)=k4_xboole_0(A_61, k2_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.49  tff(c_1165, plain, (![C_64]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_64))=k4_xboole_0('#skF_3', C_64))), inference(superposition, [status(thm), theory('equality')], [c_1018, c_1044])).
% 3.23/1.49  tff(c_1174, plain, (![C_64]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', C_64))=k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_64)))), inference(superposition, [status(thm), theory('equality')], [c_1165, c_16])).
% 3.23/1.49  tff(c_1210, plain, (![C_64]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_64))=k3_xboole_0('#skF_3', C_64))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1174])).
% 3.23/1.49  tff(c_20, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.23/1.49  tff(c_1593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1210, c_20])).
% 3.23/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.49  
% 3.23/1.49  Inference rules
% 3.23/1.49  ----------------------
% 3.23/1.49  #Ref     : 0
% 3.23/1.49  #Sup     : 393
% 3.23/1.49  #Fact    : 0
% 3.23/1.49  #Define  : 0
% 3.23/1.49  #Split   : 3
% 3.23/1.49  #Chain   : 0
% 3.23/1.49  #Close   : 0
% 3.23/1.49  
% 3.23/1.49  Ordering : KBO
% 3.23/1.49  
% 3.23/1.49  Simplification rules
% 3.23/1.49  ----------------------
% 3.23/1.49  #Subsume      : 5
% 3.23/1.49  #Demod        : 295
% 3.23/1.49  #Tautology    : 258
% 3.23/1.49  #SimpNegUnit  : 7
% 3.23/1.49  #BackRed      : 3
% 3.23/1.49  
% 3.23/1.49  #Partial instantiations: 0
% 3.23/1.49  #Strategies tried      : 1
% 3.23/1.49  
% 3.23/1.49  Timing (in seconds)
% 3.23/1.49  ----------------------
% 3.23/1.49  Preprocessing        : 0.26
% 3.23/1.49  Parsing              : 0.15
% 3.23/1.49  CNF conversion       : 0.02
% 3.23/1.49  Main loop            : 0.46
% 3.23/1.49  Inferencing          : 0.16
% 3.23/1.49  Reduction            : 0.19
% 3.23/1.49  Demodulation         : 0.15
% 3.23/1.49  BG Simplification    : 0.02
% 3.23/1.49  Subsumption          : 0.06
% 3.23/1.49  Abstraction          : 0.02
% 3.23/1.49  MUC search           : 0.00
% 3.23/1.49  Cooper               : 0.00
% 3.23/1.49  Total                : 0.75
% 3.23/1.49  Index Insertion      : 0.00
% 3.23/1.49  Index Deletion       : 0.00
% 3.23/1.49  Index Matching       : 0.00
% 3.23/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
