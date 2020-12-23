%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:55 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   44 (  47 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 (  49 expanded)
%              Number of equality atoms :   22 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_70,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | k4_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_74,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_22])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_94,plain,(
    ! [A_31,B_32] :
      ( ~ r1_xboole_0(A_31,B_32)
      | k3_xboole_0(A_31,B_32) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_98,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_94])).

tff(c_137,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_149,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_137])).

tff(c_153,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_149])).

tff(c_242,plain,(
    ! [A_39,B_40,C_41] : k4_xboole_0(k4_xboole_0(A_39,B_40),C_41) = k4_xboole_0(A_39,k2_xboole_0(B_40,C_41)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1131,plain,(
    ! [C_68] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_5',C_68)) = k4_xboole_0('#skF_3',C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_242])).

tff(c_1836,plain,(
    ! [A_80] : k4_xboole_0('#skF_3',k2_xboole_0(A_80,'#skF_5')) = k4_xboole_0('#skF_3',A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1131])).

tff(c_26,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_75,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_83,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_75])).

tff(c_1878,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1836,c_83])).

tff(c_1929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1878])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:32:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.60  
% 3.29/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.29/1.60  
% 3.29/1.60  %Foreground sorts:
% 3.29/1.60  
% 3.29/1.60  
% 3.29/1.60  %Background operators:
% 3.29/1.60  
% 3.29/1.60  
% 3.29/1.60  %Foreground operators:
% 3.29/1.60  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.29/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.29/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.29/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.29/1.60  
% 3.29/1.61  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.29/1.61  tff(f_68, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 3.29/1.61  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.29/1.61  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.29/1.61  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.29/1.61  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.29/1.61  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.29/1.61  tff(f_57, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.29/1.61  tff(c_70, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | k4_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.29/1.61  tff(c_22, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.29/1.61  tff(c_74, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_22])).
% 3.29/1.61  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.61  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.29/1.61  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.29/1.61  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.29/1.61  tff(c_88, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.61  tff(c_94, plain, (![A_31, B_32]: (~r1_xboole_0(A_31, B_32) | k3_xboole_0(A_31, B_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_88])).
% 3.29/1.61  tff(c_98, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_94])).
% 3.29/1.61  tff(c_137, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.29/1.61  tff(c_149, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_98, c_137])).
% 3.29/1.61  tff(c_153, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_149])).
% 3.29/1.61  tff(c_242, plain, (![A_39, B_40, C_41]: (k4_xboole_0(k4_xboole_0(A_39, B_40), C_41)=k4_xboole_0(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.29/1.61  tff(c_1131, plain, (![C_68]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_5', C_68))=k4_xboole_0('#skF_3', C_68))), inference(superposition, [status(thm), theory('equality')], [c_153, c_242])).
% 3.29/1.61  tff(c_1836, plain, (![A_80]: (k4_xboole_0('#skF_3', k2_xboole_0(A_80, '#skF_5'))=k4_xboole_0('#skF_3', A_80))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1131])).
% 3.29/1.61  tff(c_26, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.29/1.61  tff(c_75, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.29/1.61  tff(c_83, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_75])).
% 3.29/1.61  tff(c_1878, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1836, c_83])).
% 3.29/1.61  tff(c_1929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1878])).
% 3.29/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.61  
% 3.29/1.61  Inference rules
% 3.29/1.61  ----------------------
% 3.29/1.61  #Ref     : 0
% 3.29/1.61  #Sup     : 463
% 3.29/1.61  #Fact    : 0
% 3.29/1.61  #Define  : 0
% 3.29/1.61  #Split   : 2
% 3.29/1.61  #Chain   : 0
% 3.29/1.61  #Close   : 0
% 3.29/1.61  
% 3.29/1.61  Ordering : KBO
% 3.29/1.61  
% 3.29/1.61  Simplification rules
% 3.29/1.61  ----------------------
% 3.29/1.61  #Subsume      : 6
% 3.29/1.61  #Demod        : 378
% 3.29/1.61  #Tautology    : 272
% 3.29/1.61  #SimpNegUnit  : 6
% 3.29/1.61  #BackRed      : 1
% 3.29/1.61  
% 3.29/1.61  #Partial instantiations: 0
% 3.29/1.61  #Strategies tried      : 1
% 3.29/1.61  
% 3.29/1.61  Timing (in seconds)
% 3.29/1.61  ----------------------
% 3.29/1.61  Preprocessing        : 0.27
% 3.29/1.61  Parsing              : 0.15
% 3.29/1.61  CNF conversion       : 0.02
% 3.29/1.61  Main loop            : 0.53
% 3.29/1.61  Inferencing          : 0.18
% 3.29/1.61  Reduction            : 0.23
% 3.29/1.61  Demodulation         : 0.19
% 3.29/1.61  BG Simplification    : 0.02
% 3.29/1.61  Subsumption          : 0.07
% 3.29/1.61  Abstraction          : 0.03
% 3.29/1.62  MUC search           : 0.00
% 3.29/1.62  Cooper               : 0.00
% 3.29/1.62  Total                : 0.82
% 3.29/1.62  Index Insertion      : 0.00
% 3.29/1.62  Index Deletion       : 0.00
% 3.29/1.62  Index Matching       : 0.00
% 3.29/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
