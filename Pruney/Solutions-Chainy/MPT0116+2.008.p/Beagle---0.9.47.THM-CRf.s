%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:29 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  45 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l58_xboole_1)).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_29,plain,(
    ! [A_15,C_16,B_17] :
      ( r2_xboole_0(A_15,C_16)
      | ~ r2_xboole_0(B_17,C_16)
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,(
    ! [A_18,B_19,A_20] :
      ( r2_xboole_0(A_18,B_19)
      | ~ r1_tarski(A_18,A_20)
      | B_19 = A_20
      | ~ r1_tarski(A_20,B_19) ) ),
    inference(resolution,[status(thm)],[c_2,c_29])).

tff(c_55,plain,(
    ! [A_23,B_24,B_25] :
      ( r2_xboole_0(k4_xboole_0(A_23,B_24),B_25)
      | B_25 = A_23
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(resolution,[status(thm)],[c_10,c_33])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [A_28,B_29,B_30] :
      ( r1_tarski(k4_xboole_0(A_28,B_29),B_30)
      | B_30 = A_28
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(resolution,[status(thm)],[c_55,c_6])).

tff(c_12,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_12])).

tff(c_83,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_78])).

tff(c_101,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.20  
% 1.83/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.20  %$ r2_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.83/1.20  
% 1.83/1.20  %Foreground sorts:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Background operators:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Foreground operators:
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.20  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.20  
% 1.83/1.21  tff(f_40, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.83/1.21  tff(f_45, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 1.83/1.21  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.83/1.21  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l58_xboole_1)).
% 1.83/1.21  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.21  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.83/1.21  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.21  tff(c_29, plain, (![A_15, C_16, B_17]: (r2_xboole_0(A_15, C_16) | ~r2_xboole_0(B_17, C_16) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.83/1.21  tff(c_33, plain, (![A_18, B_19, A_20]: (r2_xboole_0(A_18, B_19) | ~r1_tarski(A_18, A_20) | B_19=A_20 | ~r1_tarski(A_20, B_19))), inference(resolution, [status(thm)], [c_2, c_29])).
% 1.83/1.21  tff(c_55, plain, (![A_23, B_24, B_25]: (r2_xboole_0(k4_xboole_0(A_23, B_24), B_25) | B_25=A_23 | ~r1_tarski(A_23, B_25))), inference(resolution, [status(thm)], [c_10, c_33])).
% 1.83/1.21  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.21  tff(c_69, plain, (![A_28, B_29, B_30]: (r1_tarski(k4_xboole_0(A_28, B_29), B_30) | B_30=A_28 | ~r1_tarski(A_28, B_30))), inference(resolution, [status(thm)], [c_55, c_6])).
% 1.83/1.21  tff(c_12, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.83/1.21  tff(c_78, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_69, c_12])).
% 1.83/1.21  tff(c_83, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_78])).
% 1.83/1.21  tff(c_101, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_12])).
% 1.83/1.21  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_101])).
% 1.83/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.21  
% 1.83/1.21  Inference rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Ref     : 0
% 1.83/1.21  #Sup     : 17
% 1.83/1.21  #Fact    : 0
% 1.83/1.21  #Define  : 0
% 1.83/1.21  #Split   : 1
% 1.83/1.21  #Chain   : 0
% 1.83/1.21  #Close   : 0
% 1.83/1.21  
% 1.83/1.21  Ordering : KBO
% 1.83/1.21  
% 1.83/1.21  Simplification rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Subsume      : 2
% 1.83/1.21  #Demod        : 11
% 1.83/1.21  #Tautology    : 3
% 1.83/1.21  #SimpNegUnit  : 0
% 1.83/1.21  #BackRed      : 5
% 1.83/1.21  
% 1.83/1.21  #Partial instantiations: 0
% 1.83/1.21  #Strategies tried      : 1
% 1.83/1.21  
% 1.83/1.21  Timing (in seconds)
% 1.83/1.21  ----------------------
% 1.83/1.21  Preprocessing        : 0.25
% 1.83/1.21  Parsing              : 0.14
% 1.83/1.21  CNF conversion       : 0.02
% 1.83/1.21  Main loop            : 0.14
% 1.83/1.21  Inferencing          : 0.06
% 1.83/1.22  Reduction            : 0.03
% 1.83/1.22  Demodulation         : 0.03
% 1.83/1.22  BG Simplification    : 0.01
% 1.83/1.22  Subsumption          : 0.04
% 1.83/1.22  Abstraction          : 0.01
% 1.83/1.22  MUC search           : 0.00
% 1.83/1.22  Cooper               : 0.00
% 1.83/1.22  Total                : 0.42
% 1.83/1.22  Index Insertion      : 0.00
% 1.83/1.22  Index Deletion       : 0.00
% 1.83/1.22  Index Matching       : 0.00
% 1.83/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
