%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:10 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   39 (  55 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  86 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_40,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( r2_xboole_0(A_20,B_21)
      | B_21 = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_53,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_16])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_20,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ r2_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_26])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_65,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(A_28,C_29)
      | ~ r1_tarski(B_30,C_29)
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_12])).

tff(c_108,plain,(
    ! [A_32] :
      ( r1_tarski(A_32,'#skF_3')
      | ~ r1_tarski(A_32,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_85])).

tff(c_114,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_114])).

tff(c_120,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_123,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_18])).

tff(c_22,plain,(
    ! [B_13,A_14] :
      ( ~ r2_xboole_0(B_13,A_14)
      | ~ r2_xboole_0(A_14,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_25,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_22])).

tff(c_48,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_25])).

tff(c_142,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_48])).

tff(c_146,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_20])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.27  
% 1.65/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.27  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.65/1.27  
% 1.65/1.27  %Foreground sorts:
% 1.65/1.27  
% 1.65/1.27  
% 1.65/1.27  %Background operators:
% 1.65/1.27  
% 1.65/1.27  
% 1.65/1.27  %Foreground operators:
% 1.65/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.65/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.27  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.65/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.27  
% 1.65/1.28  tff(f_40, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.65/1.28  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.65/1.28  tff(f_55, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.65/1.28  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.65/1.28  tff(f_44, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.65/1.28  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.65/1.28  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.65/1.28  tff(c_32, plain, (![A_20, B_21]: (r2_xboole_0(A_20, B_21) | B_21=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.65/1.28  tff(c_16, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.65/1.28  tff(c_53, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_16])).
% 1.65/1.28  tff(c_54, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_53])).
% 1.65/1.28  tff(c_20, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.65/1.28  tff(c_26, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~r2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.65/1.28  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_26])).
% 1.65/1.28  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.65/1.28  tff(c_65, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k4_xboole_0(B_25, A_24))=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.65/1.28  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.65/1.28  tff(c_85, plain, (![A_28, C_29, B_30]: (r1_tarski(A_28, C_29) | ~r1_tarski(B_30, C_29) | ~r1_tarski(A_28, B_30))), inference(superposition, [status(thm), theory('equality')], [c_65, c_12])).
% 1.65/1.28  tff(c_108, plain, (![A_32]: (r1_tarski(A_32, '#skF_3') | ~r1_tarski(A_32, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_85])).
% 1.65/1.28  tff(c_114, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_108])).
% 1.65/1.28  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_114])).
% 1.65/1.28  tff(c_120, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_53])).
% 1.65/1.28  tff(c_123, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_18])).
% 1.65/1.28  tff(c_22, plain, (![B_13, A_14]: (~r2_xboole_0(B_13, A_14) | ~r2_xboole_0(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.65/1.28  tff(c_25, plain, (~r2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_22])).
% 1.65/1.28  tff(c_48, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_25])).
% 1.65/1.28  tff(c_142, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_48])).
% 1.65/1.28  tff(c_146, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_20])).
% 1.65/1.28  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_146])).
% 1.65/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.28  
% 1.65/1.28  Inference rules
% 1.65/1.28  ----------------------
% 1.65/1.28  #Ref     : 0
% 1.65/1.28  #Sup     : 27
% 1.65/1.28  #Fact    : 0
% 1.65/1.28  #Define  : 0
% 1.65/1.28  #Split   : 3
% 1.65/1.28  #Chain   : 0
% 1.65/1.28  #Close   : 0
% 1.65/1.28  
% 1.65/1.28  Ordering : KBO
% 1.65/1.28  
% 1.65/1.28  Simplification rules
% 1.65/1.28  ----------------------
% 1.65/1.28  #Subsume      : 5
% 1.65/1.28  #Demod        : 10
% 1.65/1.28  #Tautology    : 10
% 1.65/1.28  #SimpNegUnit  : 2
% 1.65/1.28  #BackRed      : 6
% 1.65/1.28  
% 1.65/1.28  #Partial instantiations: 0
% 1.65/1.28  #Strategies tried      : 1
% 1.65/1.28  
% 1.65/1.28  Timing (in seconds)
% 1.65/1.28  ----------------------
% 1.65/1.28  Preprocessing        : 0.23
% 1.65/1.28  Parsing              : 0.12
% 1.65/1.28  CNF conversion       : 0.02
% 1.65/1.28  Main loop            : 0.14
% 1.65/1.28  Inferencing          : 0.06
% 1.65/1.28  Reduction            : 0.04
% 1.65/1.28  Demodulation         : 0.02
% 1.65/1.28  BG Simplification    : 0.01
% 1.65/1.28  Subsumption          : 0.03
% 1.65/1.28  Abstraction          : 0.01
% 1.65/1.28  MUC search           : 0.00
% 1.65/1.28  Cooper               : 0.00
% 1.65/1.28  Total                : 0.40
% 1.65/1.28  Index Insertion      : 0.00
% 1.65/1.28  Index Deletion       : 0.00
% 1.65/1.28  Index Matching       : 0.00
% 1.65/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
