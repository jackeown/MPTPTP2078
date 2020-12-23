%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:24 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  58 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_143,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(A_27,C_28)
      | ~ r1_tarski(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_122,plain,(
    ! [A_33,A_34,B_35] :
      ( r1_tarski(A_33,A_34)
      | ~ r1_tarski(A_33,k4_xboole_0(A_34,B_35)) ) ),
    inference(resolution,[status(thm)],[c_8,c_87])).

tff(c_135,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_122])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_135])).

tff(c_141,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_147,plain,(
    k4_xboole_0('#skF_1','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_143,c_141])).

tff(c_142,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_153,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_163,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_142,c_153])).

tff(c_290,plain,(
    ! [A_58,B_59,C_60] : k4_xboole_0(k3_xboole_0(A_58,B_59),C_60) = k3_xboole_0(A_58,k4_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_322,plain,(
    ! [C_61] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_61)) = k4_xboole_0('#skF_1',C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_290])).

tff(c_165,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_153])).

tff(c_334,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_165])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:14:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.23  
% 2.02/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.24  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.02/1.24  
% 2.02/1.24  %Foreground sorts:
% 2.02/1.24  
% 2.02/1.24  
% 2.02/1.24  %Background operators:
% 2.02/1.24  
% 2.02/1.24  
% 2.02/1.24  %Foreground operators:
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.02/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.24  
% 2.02/1.25  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.02/1.25  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.02/1.25  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.02/1.25  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.02/1.25  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.02/1.25  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.02/1.25  tff(c_143, plain, (![A_36, B_37]: (r1_xboole_0(A_36, B_37) | k4_xboole_0(A_36, B_37)!=A_36)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.25  tff(c_16, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.25  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_16])).
% 2.02/1.25  tff(c_18, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.25  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.25  tff(c_87, plain, (![A_27, C_28, B_29]: (r1_tarski(A_27, C_28) | ~r1_tarski(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.25  tff(c_122, plain, (![A_33, A_34, B_35]: (r1_tarski(A_33, A_34) | ~r1_tarski(A_33, k4_xboole_0(A_34, B_35)))), inference(resolution, [status(thm)], [c_8, c_87])).
% 2.02/1.25  tff(c_135, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_122])).
% 2.02/1.25  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_135])).
% 2.02/1.25  tff(c_141, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_16])).
% 2.02/1.25  tff(c_147, plain, (k4_xboole_0('#skF_1', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_143, c_141])).
% 2.02/1.25  tff(c_142, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_16])).
% 2.02/1.25  tff(c_153, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.25  tff(c_163, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_142, c_153])).
% 2.02/1.25  tff(c_290, plain, (![A_58, B_59, C_60]: (k4_xboole_0(k3_xboole_0(A_58, B_59), C_60)=k3_xboole_0(A_58, k4_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.25  tff(c_322, plain, (![C_61]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_61))=k4_xboole_0('#skF_1', C_61))), inference(superposition, [status(thm), theory('equality')], [c_163, c_290])).
% 2.02/1.25  tff(c_165, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_18, c_153])).
% 2.02/1.25  tff(c_334, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_322, c_165])).
% 2.02/1.25  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_334])).
% 2.02/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.25  
% 2.02/1.25  Inference rules
% 2.02/1.25  ----------------------
% 2.02/1.25  #Ref     : 0
% 2.02/1.25  #Sup     : 87
% 2.02/1.25  #Fact    : 0
% 2.02/1.25  #Define  : 0
% 2.02/1.25  #Split   : 1
% 2.02/1.25  #Chain   : 0
% 2.02/1.25  #Close   : 0
% 2.02/1.25  
% 2.02/1.25  Ordering : KBO
% 2.02/1.25  
% 2.02/1.25  Simplification rules
% 2.02/1.25  ----------------------
% 2.02/1.25  #Subsume      : 2
% 2.02/1.25  #Demod        : 11
% 2.02/1.25  #Tautology    : 34
% 2.02/1.25  #SimpNegUnit  : 2
% 2.02/1.25  #BackRed      : 0
% 2.02/1.25  
% 2.02/1.25  #Partial instantiations: 0
% 2.02/1.25  #Strategies tried      : 1
% 2.02/1.25  
% 2.02/1.25  Timing (in seconds)
% 2.02/1.25  ----------------------
% 2.02/1.25  Preprocessing        : 0.27
% 2.02/1.25  Parsing              : 0.15
% 2.02/1.25  CNF conversion       : 0.01
% 2.02/1.25  Main loop            : 0.20
% 2.02/1.25  Inferencing          : 0.08
% 2.02/1.25  Reduction            : 0.06
% 2.02/1.25  Demodulation         : 0.04
% 2.02/1.25  BG Simplification    : 0.01
% 2.02/1.25  Subsumption          : 0.03
% 2.02/1.25  Abstraction          : 0.01
% 2.02/1.25  MUC search           : 0.00
% 2.02/1.25  Cooper               : 0.00
% 2.02/1.25  Total                : 0.50
% 2.02/1.25  Index Insertion      : 0.00
% 2.02/1.25  Index Deletion       : 0.00
% 2.02/1.25  Index Matching       : 0.00
% 2.02/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
