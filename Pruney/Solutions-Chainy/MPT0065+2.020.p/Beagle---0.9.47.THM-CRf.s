%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:12 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   48 (  74 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 ( 108 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_8,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_37,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_37])).

tff(c_48,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_48])).

tff(c_385,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,k4_xboole_0(B_41,A_40)) = B_41
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_403,plain,(
    ! [A_12] :
      ( k2_xboole_0(A_12,k1_xboole_0) = A_12
      | ~ r1_tarski(A_12,A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_385])).

tff(c_415,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_403])).

tff(c_26,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ r2_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_42])).

tff(c_91,plain,(
    ! [A_26,B_27] :
      ( r2_xboole_0(A_26,B_27)
      | B_27 = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_22])).

tff(c_143,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_236,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_tarski(A_33,C_34)
      | ~ r1_tarski(B_35,C_34)
      | ~ r1_tarski(A_33,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_255,plain,(
    ! [A_36] :
      ( r1_tarski(A_36,'#skF_3')
      | ~ r1_tarski(A_36,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_236])).

tff(c_266,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_255])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_266])).

tff(c_282,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_68,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_284,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_68])).

tff(c_400,plain,
    ( k2_xboole_0('#skF_1',k1_xboole_0) = '#skF_2'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_385])).

tff(c_413,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_400])).

tff(c_445,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_413])).

tff(c_480,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_26])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:34:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.22  
% 1.95/1.22  %Foreground sorts:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Background operators:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Foreground operators:
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.22  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.22  
% 2.06/1.23  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.06/1.23  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.06/1.23  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.06/1.23  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.06/1.23  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.06/1.23  tff(f_60, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_xboole_1)).
% 2.06/1.23  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.06/1.23  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.06/1.23  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.23  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.23  tff(c_37, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.23  tff(c_40, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_37])).
% 2.06/1.23  tff(c_48, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.23  tff(c_66, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_48])).
% 2.06/1.23  tff(c_385, plain, (![A_40, B_41]: (k2_xboole_0(A_40, k4_xboole_0(B_41, A_40))=B_41 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.06/1.23  tff(c_403, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12 | ~r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_66, c_385])).
% 2.06/1.23  tff(c_415, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_403])).
% 2.06/1.23  tff(c_26, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.23  tff(c_42, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~r2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.23  tff(c_46, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_42])).
% 2.06/1.23  tff(c_91, plain, (![A_26, B_27]: (r2_xboole_0(A_26, B_27) | B_27=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.23  tff(c_22, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.23  tff(c_103, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_91, c_22])).
% 2.06/1.23  tff(c_143, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_103])).
% 2.06/1.23  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.23  tff(c_236, plain, (![A_33, C_34, B_35]: (r1_tarski(A_33, C_34) | ~r1_tarski(B_35, C_34) | ~r1_tarski(A_33, B_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.23  tff(c_255, plain, (![A_36]: (r1_tarski(A_36, '#skF_3') | ~r1_tarski(A_36, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_236])).
% 2.06/1.23  tff(c_266, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_255])).
% 2.06/1.23  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_266])).
% 2.06/1.23  tff(c_282, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_103])).
% 2.06/1.23  tff(c_68, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_48])).
% 2.06/1.23  tff(c_284, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_282, c_68])).
% 2.06/1.23  tff(c_400, plain, (k2_xboole_0('#skF_1', k1_xboole_0)='#skF_2' | ~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_284, c_385])).
% 2.06/1.23  tff(c_413, plain, (k2_xboole_0('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_400])).
% 2.06/1.23  tff(c_445, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_415, c_413])).
% 2.06/1.23  tff(c_480, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_26])).
% 2.06/1.23  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_480])).
% 2.06/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  Inference rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Ref     : 0
% 2.06/1.23  #Sup     : 110
% 2.06/1.23  #Fact    : 0
% 2.06/1.23  #Define  : 0
% 2.06/1.23  #Split   : 1
% 2.06/1.23  #Chain   : 0
% 2.06/1.23  #Close   : 0
% 2.06/1.23  
% 2.06/1.23  Ordering : KBO
% 2.06/1.23  
% 2.06/1.23  Simplification rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Subsume      : 2
% 2.06/1.23  #Demod        : 59
% 2.06/1.23  #Tautology    : 91
% 2.06/1.23  #SimpNegUnit  : 2
% 2.06/1.23  #BackRed      : 10
% 2.06/1.23  
% 2.06/1.23  #Partial instantiations: 0
% 2.06/1.23  #Strategies tried      : 1
% 2.06/1.23  
% 2.06/1.23  Timing (in seconds)
% 2.06/1.23  ----------------------
% 2.09/1.23  Preprocessing        : 0.26
% 2.09/1.23  Parsing              : 0.15
% 2.09/1.23  CNF conversion       : 0.02
% 2.09/1.23  Main loop            : 0.22
% 2.09/1.23  Inferencing          : 0.09
% 2.09/1.23  Reduction            : 0.07
% 2.09/1.23  Demodulation         : 0.05
% 2.09/1.23  BG Simplification    : 0.01
% 2.09/1.23  Subsumption          : 0.04
% 2.09/1.23  Abstraction          : 0.01
% 2.09/1.23  MUC search           : 0.00
% 2.09/1.23  Cooper               : 0.00
% 2.09/1.23  Total                : 0.50
% 2.09/1.23  Index Insertion      : 0.00
% 2.09/1.23  Index Deletion       : 0.00
% 2.09/1.23  Index Matching       : 0.00
% 2.09/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
