%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:12 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   34 (  56 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 ( 101 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l58_xboole_1)).

tff(c_21,plain,(
    ! [A_9,B_10] :
      ( r2_xboole_0(A_9,B_10)
      | B_10 = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_33,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_21,c_10])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_33])).

tff(c_12,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_16])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [A_11,C_12,B_13] :
      ( r2_xboole_0(A_11,C_12)
      | ~ r2_xboole_0(B_13,C_12)
      | ~ r1_tarski(A_11,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,(
    ! [A_18,B_19,A_20] :
      ( r2_xboole_0(A_18,B_19)
      | ~ r1_tarski(A_18,A_20)
      | B_19 = A_20
      | ~ r1_tarski(A_20,B_19) ) ),
    inference(resolution,[status(thm)],[c_2,c_37])).

tff(c_81,plain,(
    ! [B_21] :
      ( r2_xboole_0('#skF_1',B_21)
      | B_21 = '#skF_2'
      | ~ r1_tarski('#skF_2',B_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_71])).

tff(c_89,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_81,c_10])).

tff(c_98,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_105,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_20])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_105])).

tff(c_110,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_113,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_12])).

tff(c_119,plain,(
    ! [A_22,C_23,B_24] :
      ( r2_xboole_0(A_22,C_23)
      | ~ r2_xboole_0(B_24,C_23)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,(
    ! [A_25] :
      ( r2_xboole_0(A_25,'#skF_2')
      | ~ r1_tarski(A_25,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_119])).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_126,c_4])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:40:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.18  
% 1.77/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.18  %$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.77/1.18  
% 1.77/1.18  %Foreground sorts:
% 1.77/1.18  
% 1.77/1.18  
% 1.77/1.18  %Background operators:
% 1.77/1.18  
% 1.77/1.18  
% 1.77/1.18  %Foreground operators:
% 1.77/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.18  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.77/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.18  
% 1.83/1.19  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.83/1.19  tff(f_45, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.83/1.19  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l58_xboole_1)).
% 1.83/1.19  tff(c_21, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.19  tff(c_10, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.83/1.19  tff(c_33, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_21, c_10])).
% 1.83/1.19  tff(c_36, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_33])).
% 1.83/1.19  tff(c_12, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.83/1.19  tff(c_14, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.83/1.19  tff(c_16, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.19  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_14, c_16])).
% 1.83/1.19  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.19  tff(c_37, plain, (![A_11, C_12, B_13]: (r2_xboole_0(A_11, C_12) | ~r2_xboole_0(B_13, C_12) | ~r1_tarski(A_11, B_13))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.83/1.19  tff(c_71, plain, (![A_18, B_19, A_20]: (r2_xboole_0(A_18, B_19) | ~r1_tarski(A_18, A_20) | B_19=A_20 | ~r1_tarski(A_20, B_19))), inference(resolution, [status(thm)], [c_2, c_37])).
% 1.83/1.19  tff(c_81, plain, (![B_21]: (r2_xboole_0('#skF_1', B_21) | B_21='#skF_2' | ~r1_tarski('#skF_2', B_21))), inference(resolution, [status(thm)], [c_20, c_71])).
% 1.83/1.19  tff(c_89, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_81, c_10])).
% 1.83/1.19  tff(c_98, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89])).
% 1.83/1.19  tff(c_105, plain, (r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_20])).
% 1.83/1.19  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_105])).
% 1.83/1.19  tff(c_110, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_33])).
% 1.83/1.19  tff(c_113, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_12])).
% 1.83/1.19  tff(c_119, plain, (![A_22, C_23, B_24]: (r2_xboole_0(A_22, C_23) | ~r2_xboole_0(B_24, C_23) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.83/1.19  tff(c_126, plain, (![A_25]: (r2_xboole_0(A_25, '#skF_2') | ~r1_tarski(A_25, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_119])).
% 1.83/1.19  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.19  tff(c_135, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_126, c_4])).
% 1.83/1.19  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_135])).
% 1.83/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  Inference rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Ref     : 0
% 1.83/1.19  #Sup     : 26
% 1.83/1.19  #Fact    : 0
% 1.83/1.19  #Define  : 0
% 1.83/1.19  #Split   : 1
% 1.83/1.19  #Chain   : 0
% 1.83/1.19  #Close   : 0
% 1.83/1.19  
% 1.83/1.19  Ordering : KBO
% 1.83/1.19  
% 1.83/1.19  Simplification rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Subsume      : 5
% 1.83/1.19  #Demod        : 15
% 1.83/1.19  #Tautology    : 4
% 1.83/1.19  #SimpNegUnit  : 2
% 1.83/1.19  #BackRed      : 10
% 1.83/1.19  
% 1.83/1.19  #Partial instantiations: 0
% 1.83/1.19  #Strategies tried      : 1
% 1.83/1.19  
% 1.83/1.19  Timing (in seconds)
% 1.83/1.19  ----------------------
% 1.83/1.19  Preprocessing        : 0.24
% 1.83/1.19  Parsing              : 0.13
% 1.83/1.19  CNF conversion       : 0.01
% 1.83/1.19  Main loop            : 0.19
% 1.83/1.19  Inferencing          : 0.07
% 1.83/1.19  Reduction            : 0.05
% 1.83/1.19  Demodulation         : 0.04
% 1.83/1.20  BG Simplification    : 0.01
% 1.83/1.20  Subsumption          : 0.05
% 1.83/1.20  Abstraction          : 0.01
% 1.83/1.20  MUC search           : 0.00
% 1.83/1.20  Cooper               : 0.00
% 1.83/1.20  Total                : 0.46
% 1.83/1.20  Index Insertion      : 0.00
% 1.83/1.20  Index Deletion       : 0.00
% 1.83/1.20  Index Matching       : 0.00
% 1.83/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
