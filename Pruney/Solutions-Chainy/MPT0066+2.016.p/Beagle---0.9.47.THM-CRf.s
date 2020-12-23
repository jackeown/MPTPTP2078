%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:14 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   34 (  56 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  99 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    7 (   3 average)
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
        ( ( r1_tarski(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r1_tarski(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

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

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_16])).

tff(c_37,plain,(
    ! [A_11,C_12,B_13] :
      ( r2_xboole_0(A_11,C_12)
      | ~ r1_tarski(B_13,C_12)
      | ~ r2_xboole_0(A_11,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [A_15] :
      ( r2_xboole_0(A_15,'#skF_3')
      | ~ r2_xboole_0(A_15,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_37])).

tff(c_104,plain,(
    ! [A_20] :
      ( r2_xboole_0(A_20,'#skF_3')
      | A_20 = '#skF_2'
      | ~ r1_tarski(A_20,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2,c_59])).

tff(c_110,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_10])).

tff(c_118,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_110])).

tff(c_127,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_20])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_127])).

tff(c_132,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_136,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_12])).

tff(c_141,plain,(
    ! [A_21,C_22,B_23] :
      ( r2_xboole_0(A_21,C_22)
      | ~ r1_tarski(B_23,C_22)
      | ~ r2_xboole_0(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_157,plain,(
    ! [A_24] :
      ( r2_xboole_0(A_24,'#skF_2')
      | ~ r2_xboole_0(A_24,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_141])).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_164,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_157,c_4])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:34:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.25  
% 1.91/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.25  %$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.91/1.25  
% 1.91/1.25  %Foreground sorts:
% 1.91/1.25  
% 1.91/1.25  
% 1.91/1.25  %Background operators:
% 1.91/1.25  
% 1.91/1.25  
% 1.91/1.25  %Foreground operators:
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.25  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.25  
% 1.91/1.26  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.91/1.26  tff(f_45, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 1.91/1.26  tff(f_38, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.91/1.26  tff(c_21, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.26  tff(c_10, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.91/1.26  tff(c_33, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_21, c_10])).
% 1.91/1.26  tff(c_36, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_33])).
% 1.91/1.26  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.91/1.26  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.26  tff(c_12, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.91/1.26  tff(c_16, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.26  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_16])).
% 1.91/1.26  tff(c_37, plain, (![A_11, C_12, B_13]: (r2_xboole_0(A_11, C_12) | ~r1_tarski(B_13, C_12) | ~r2_xboole_0(A_11, B_13))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.26  tff(c_59, plain, (![A_15]: (r2_xboole_0(A_15, '#skF_3') | ~r2_xboole_0(A_15, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_37])).
% 1.91/1.26  tff(c_104, plain, (![A_20]: (r2_xboole_0(A_20, '#skF_3') | A_20='#skF_2' | ~r1_tarski(A_20, '#skF_2'))), inference(resolution, [status(thm)], [c_2, c_59])).
% 1.91/1.26  tff(c_110, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_104, c_10])).
% 1.91/1.26  tff(c_118, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_110])).
% 1.91/1.26  tff(c_127, plain, (r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_20])).
% 1.91/1.26  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_127])).
% 1.91/1.26  tff(c_132, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_33])).
% 1.91/1.26  tff(c_136, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_12])).
% 1.91/1.26  tff(c_141, plain, (![A_21, C_22, B_23]: (r2_xboole_0(A_21, C_22) | ~r1_tarski(B_23, C_22) | ~r2_xboole_0(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.26  tff(c_157, plain, (![A_24]: (r2_xboole_0(A_24, '#skF_2') | ~r2_xboole_0(A_24, '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_141])).
% 1.91/1.26  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.26  tff(c_164, plain, (~r2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_157, c_4])).
% 1.91/1.26  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_164])).
% 1.91/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.26  
% 1.91/1.26  Inference rules
% 1.91/1.26  ----------------------
% 1.91/1.26  #Ref     : 0
% 1.91/1.26  #Sup     : 29
% 1.91/1.26  #Fact    : 0
% 1.91/1.26  #Define  : 0
% 1.91/1.26  #Split   : 3
% 1.91/1.26  #Chain   : 0
% 1.91/1.26  #Close   : 0
% 1.91/1.26  
% 1.91/1.26  Ordering : KBO
% 1.91/1.26  
% 1.91/1.26  Simplification rules
% 1.91/1.26  ----------------------
% 1.91/1.26  #Subsume      : 5
% 1.91/1.26  #Demod        : 18
% 1.91/1.26  #Tautology    : 8
% 1.91/1.26  #SimpNegUnit  : 1
% 1.91/1.26  #BackRed      : 11
% 1.91/1.26  
% 1.91/1.26  #Partial instantiations: 0
% 1.91/1.26  #Strategies tried      : 1
% 1.91/1.26  
% 1.91/1.26  Timing (in seconds)
% 1.91/1.26  ----------------------
% 1.91/1.27  Preprocessing        : 0.27
% 1.91/1.27  Parsing              : 0.15
% 1.91/1.27  CNF conversion       : 0.02
% 1.91/1.27  Main loop            : 0.17
% 1.91/1.27  Inferencing          : 0.07
% 1.91/1.27  Reduction            : 0.04
% 1.91/1.27  Demodulation         : 0.03
% 1.91/1.27  BG Simplification    : 0.01
% 1.91/1.27  Subsumption          : 0.04
% 1.91/1.27  Abstraction          : 0.01
% 1.91/1.27  MUC search           : 0.00
% 1.91/1.27  Cooper               : 0.00
% 1.91/1.27  Total                : 0.47
% 1.91/1.27  Index Insertion      : 0.00
% 1.91/1.27  Index Deletion       : 0.00
% 1.91/1.27  Index Matching       : 0.00
% 1.91/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
