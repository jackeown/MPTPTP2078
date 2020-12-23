%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:23 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  55 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_25,plain,(
    ! [A_21,B_22] :
      ( k2_xboole_0(A_21,B_22) = B_22
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_35,plain,(
    ! [A_6,B_7] : k2_xboole_0(k4_xboole_0(A_6,B_7),A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_10,c_25])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_60])).

tff(c_179,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski(A_39,k2_xboole_0(B_40,C_41))
      | ~ r1_tarski(k4_xboole_0(A_39,B_40),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_186,plain,(
    ! [C_41] :
      ( r1_tarski('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_41))
      | ~ r1_tarski(k1_xboole_0,C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_179])).

tff(c_634,plain,(
    ! [C_68] : r1_tarski('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_186])).

tff(c_648,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_634])).

tff(c_653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_648])).

tff(c_654,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_811,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_xboole_0(A_82,C_83)
      | ~ r1_xboole_0(B_84,C_83)
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_834,plain,(
    ! [A_87,B_88,A_89] :
      ( r1_xboole_0(A_87,B_88)
      | ~ r1_tarski(A_87,k4_xboole_0(A_89,B_88)) ) ),
    inference(resolution,[status(thm)],[c_16,c_811])).

tff(c_857,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_834])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_654,c_857])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.40  
% 2.50/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.40  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.40  
% 2.50/1.40  %Foreground sorts:
% 2.50/1.40  
% 2.50/1.40  
% 2.50/1.40  %Background operators:
% 2.50/1.40  
% 2.50/1.40  
% 2.50/1.40  %Foreground operators:
% 2.50/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.50/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.50/1.40  
% 2.50/1.41  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.50/1.41  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.50/1.41  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.50/1.41  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.50/1.41  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.50/1.41  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.50/1.41  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.50/1.41  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.50/1.41  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.50/1.41  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_18])).
% 2.50/1.41  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.50/1.41  tff(c_25, plain, (![A_21, B_22]: (k2_xboole_0(A_21, B_22)=B_22 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.50/1.41  tff(c_35, plain, (![A_6, B_7]: (k2_xboole_0(k4_xboole_0(A_6, B_7), A_6)=A_6)), inference(resolution, [status(thm)], [c_10, c_25])).
% 2.50/1.41  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.50/1.41  tff(c_20, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.50/1.41  tff(c_60, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.41  tff(c_71, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_60])).
% 2.50/1.41  tff(c_179, plain, (![A_39, B_40, C_41]: (r1_tarski(A_39, k2_xboole_0(B_40, C_41)) | ~r1_tarski(k4_xboole_0(A_39, B_40), C_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.41  tff(c_186, plain, (![C_41]: (r1_tarski('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_41)) | ~r1_tarski(k1_xboole_0, C_41))), inference(superposition, [status(thm), theory('equality')], [c_71, c_179])).
% 2.50/1.41  tff(c_634, plain, (![C_68]: (r1_tarski('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_68)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_186])).
% 2.50/1.41  tff(c_648, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35, c_634])).
% 2.50/1.41  tff(c_653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_648])).
% 2.50/1.41  tff(c_654, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 2.50/1.41  tff(c_16, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.50/1.41  tff(c_811, plain, (![A_82, C_83, B_84]: (r1_xboole_0(A_82, C_83) | ~r1_xboole_0(B_84, C_83) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.41  tff(c_834, plain, (![A_87, B_88, A_89]: (r1_xboole_0(A_87, B_88) | ~r1_tarski(A_87, k4_xboole_0(A_89, B_88)))), inference(resolution, [status(thm)], [c_16, c_811])).
% 2.50/1.41  tff(c_857, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_834])).
% 2.50/1.41  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_654, c_857])).
% 2.50/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.41  
% 2.50/1.41  Inference rules
% 2.50/1.41  ----------------------
% 2.50/1.41  #Ref     : 0
% 2.50/1.41  #Sup     : 210
% 2.50/1.41  #Fact    : 0
% 2.50/1.41  #Define  : 0
% 2.50/1.41  #Split   : 1
% 2.50/1.41  #Chain   : 0
% 2.50/1.41  #Close   : 0
% 2.50/1.41  
% 2.50/1.41  Ordering : KBO
% 2.50/1.41  
% 2.50/1.41  Simplification rules
% 2.50/1.41  ----------------------
% 2.50/1.41  #Subsume      : 8
% 2.50/1.41  #Demod        : 94
% 2.50/1.41  #Tautology    : 129
% 2.50/1.41  #SimpNegUnit  : 2
% 2.50/1.41  #BackRed      : 0
% 2.50/1.41  
% 2.50/1.41  #Partial instantiations: 0
% 2.50/1.41  #Strategies tried      : 1
% 2.50/1.41  
% 2.50/1.41  Timing (in seconds)
% 2.50/1.41  ----------------------
% 2.50/1.41  Preprocessing        : 0.30
% 2.50/1.41  Parsing              : 0.18
% 2.50/1.41  CNF conversion       : 0.02
% 2.50/1.41  Main loop            : 0.32
% 2.50/1.41  Inferencing          : 0.13
% 2.50/1.41  Reduction            : 0.10
% 2.50/1.41  Demodulation         : 0.07
% 2.50/1.41  BG Simplification    : 0.02
% 2.50/1.41  Subsumption          : 0.05
% 2.50/1.41  Abstraction          : 0.01
% 2.50/1.41  MUC search           : 0.00
% 2.50/1.41  Cooper               : 0.00
% 2.50/1.41  Total                : 0.64
% 2.50/1.41  Index Insertion      : 0.00
% 2.50/1.41  Index Deletion       : 0.00
% 2.50/1.41  Index Matching       : 0.00
% 2.50/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
