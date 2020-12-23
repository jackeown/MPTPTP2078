%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:19 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   40 (  58 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  57 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_113,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_109])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_13,B_14] : k3_xboole_0(k4_xboole_0(A_13,B_14),B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_41])).

tff(c_121,plain,(
    ! [A_28] : k3_xboole_0(k1_xboole_0,A_28) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_48])).

tff(c_222,plain,(
    ! [A_34] : k3_xboole_0(k1_xboole_0,A_34) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_48])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k3_xboole_0(A_7,B_8),C_9) = k3_xboole_0(A_7,k4_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_227,plain,(
    ! [A_34,C_9] : k3_xboole_0(k1_xboole_0,k4_xboole_0(A_34,C_9)) = k4_xboole_0(k1_xboole_0,C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_12])).

tff(c_245,plain,(
    ! [C_9] : k4_xboole_0(k1_xboole_0,C_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_227])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_41])).

tff(c_164,plain,(
    ! [A_31,B_32,C_33] : k4_xboole_0(k3_xboole_0(A_31,B_32),C_33) = k3_xboole_0(A_31,k4_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_208,plain,(
    ! [C_33] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_33)) = k4_xboole_0(k1_xboole_0,C_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_164])).

tff(c_299,plain,(
    ! [C_33] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_33)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_208])).

tff(c_79,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k3_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79,c_18])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.53  
% 2.33/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.53  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.36/1.53  
% 2.36/1.53  %Foreground sorts:
% 2.36/1.53  
% 2.36/1.53  
% 2.36/1.53  %Background operators:
% 2.36/1.53  
% 2.36/1.53  
% 2.36/1.53  %Foreground operators:
% 2.36/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.36/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.53  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.36/1.53  
% 2.36/1.55  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.36/1.55  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.36/1.55  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.36/1.55  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.36/1.55  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.36/1.55  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.36/1.55  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 2.36/1.55  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.55  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.55  tff(c_88, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.55  tff(c_109, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_88])).
% 2.36/1.55  tff(c_113, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_109])).
% 2.36/1.55  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.36/1.55  tff(c_41, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.55  tff(c_48, plain, (![A_13, B_14]: (k3_xboole_0(k4_xboole_0(A_13, B_14), B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_41])).
% 2.36/1.55  tff(c_121, plain, (![A_28]: (k3_xboole_0(k1_xboole_0, A_28)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_113, c_48])).
% 2.36/1.55  tff(c_222, plain, (![A_34]: (k3_xboole_0(k1_xboole_0, A_34)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_113, c_48])).
% 2.36/1.55  tff(c_12, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k3_xboole_0(A_7, B_8), C_9)=k3_xboole_0(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.55  tff(c_227, plain, (![A_34, C_9]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(A_34, C_9))=k4_xboole_0(k1_xboole_0, C_9))), inference(superposition, [status(thm), theory('equality')], [c_222, c_12])).
% 2.36/1.55  tff(c_245, plain, (![C_9]: (k4_xboole_0(k1_xboole_0, C_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_227])).
% 2.36/1.55  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.55  tff(c_49, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_41])).
% 2.36/1.55  tff(c_164, plain, (![A_31, B_32, C_33]: (k4_xboole_0(k3_xboole_0(A_31, B_32), C_33)=k3_xboole_0(A_31, k4_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.55  tff(c_208, plain, (![C_33]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_33))=k4_xboole_0(k1_xboole_0, C_33))), inference(superposition, [status(thm), theory('equality')], [c_49, c_164])).
% 2.36/1.55  tff(c_299, plain, (![C_33]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_33))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_245, c_208])).
% 2.36/1.55  tff(c_79, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k3_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.55  tff(c_18, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.55  tff(c_87, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_79, c_18])).
% 2.36/1.55  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_299, c_87])).
% 2.36/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.55  
% 2.36/1.55  Inference rules
% 2.36/1.55  ----------------------
% 2.36/1.55  #Ref     : 0
% 2.36/1.55  #Sup     : 69
% 2.36/1.55  #Fact    : 0
% 2.36/1.55  #Define  : 0
% 2.36/1.55  #Split   : 0
% 2.36/1.55  #Chain   : 0
% 2.36/1.55  #Close   : 0
% 2.36/1.55  
% 2.36/1.55  Ordering : KBO
% 2.36/1.55  
% 2.36/1.55  Simplification rules
% 2.36/1.55  ----------------------
% 2.36/1.55  #Subsume      : 0
% 2.36/1.55  #Demod        : 18
% 2.36/1.55  #Tautology    : 45
% 2.36/1.55  #SimpNegUnit  : 0
% 2.36/1.55  #BackRed      : 1
% 2.36/1.55  
% 2.36/1.55  #Partial instantiations: 0
% 2.36/1.55  #Strategies tried      : 1
% 2.36/1.55  
% 2.36/1.55  Timing (in seconds)
% 2.36/1.55  ----------------------
% 2.36/1.55  Preprocessing        : 0.46
% 2.36/1.55  Parsing              : 0.24
% 2.36/1.55  CNF conversion       : 0.03
% 2.36/1.55  Main loop            : 0.27
% 2.36/1.55  Inferencing          : 0.11
% 2.36/1.55  Reduction            : 0.09
% 2.36/1.55  Demodulation         : 0.07
% 2.36/1.55  BG Simplification    : 0.02
% 2.36/1.56  Subsumption          : 0.04
% 2.36/1.56  Abstraction          : 0.02
% 2.36/1.56  MUC search           : 0.00
% 2.36/1.56  Cooper               : 0.00
% 2.36/1.56  Total                : 0.77
% 2.36/1.56  Index Insertion      : 0.00
% 2.36/1.56  Index Deletion       : 0.00
% 2.36/1.56  Index Matching       : 0.00
% 2.36/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
