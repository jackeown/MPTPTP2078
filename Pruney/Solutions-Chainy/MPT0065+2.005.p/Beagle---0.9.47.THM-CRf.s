%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:10 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   34 (  50 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  81 expanded)
%              Number of equality atoms :    6 (  12 expanded)
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

tff(f_40,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_10,plain,(
    ! [A_5] : ~ r2_xboole_0(A_5,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_29,plain,(
    ! [A_15,B_16] :
      ( r2_xboole_0(A_15,B_16)
      | B_16 = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_29,c_14])).

tff(c_51,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_18,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_24])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_69,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,C_22)
      | ~ r1_tarski(B_23,C_22)
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,'#skF_3')
      | ~ r1_tarski(A_24,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_69])).

tff(c_80,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_80])).

tff(c_85,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_88,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_16])).

tff(c_20,plain,(
    ! [B_11,A_12] :
      ( ~ r2_xboole_0(B_11,A_12)
      | ~ r2_xboole_0(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_23,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_20])).

tff(c_45,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_29,c_23])).

tff(c_95,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_45])).

tff(c_99,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_18])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:35:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.18  
% 1.60/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.18  %$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.60/1.18  
% 1.60/1.18  %Foreground sorts:
% 1.60/1.18  
% 1.60/1.18  
% 1.60/1.18  %Background operators:
% 1.60/1.18  
% 1.60/1.18  
% 1.60/1.18  %Foreground operators:
% 1.60/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.18  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.60/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.18  
% 1.80/1.19  tff(f_40, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.80/1.19  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.80/1.19  tff(f_53, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.80/1.19  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.80/1.19  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.80/1.19  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.80/1.19  tff(c_29, plain, (![A_15, B_16]: (r2_xboole_0(A_15, B_16) | B_16=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.80/1.19  tff(c_14, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.80/1.19  tff(c_48, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_29, c_14])).
% 1.80/1.19  tff(c_51, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 1.80/1.19  tff(c_18, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.80/1.19  tff(c_24, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.80/1.19  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_24])).
% 1.80/1.19  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.80/1.19  tff(c_69, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, C_22) | ~r1_tarski(B_23, C_22) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.80/1.19  tff(c_77, plain, (![A_24]: (r1_tarski(A_24, '#skF_3') | ~r1_tarski(A_24, '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_69])).
% 1.80/1.19  tff(c_80, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_77])).
% 1.80/1.19  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_80])).
% 1.80/1.19  tff(c_85, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_48])).
% 1.80/1.19  tff(c_88, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_16])).
% 1.80/1.19  tff(c_20, plain, (![B_11, A_12]: (~r2_xboole_0(B_11, A_12) | ~r2_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.80/1.19  tff(c_23, plain, (~r2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_18, c_20])).
% 1.80/1.19  tff(c_45, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_29, c_23])).
% 1.80/1.19  tff(c_95, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_45])).
% 1.80/1.19  tff(c_99, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_18])).
% 1.80/1.19  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_99])).
% 1.80/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.19  
% 1.80/1.19  Inference rules
% 1.80/1.19  ----------------------
% 1.80/1.19  #Ref     : 0
% 1.80/1.19  #Sup     : 16
% 1.80/1.19  #Fact    : 0
% 1.80/1.19  #Define  : 0
% 1.80/1.19  #Split   : 3
% 1.80/1.19  #Chain   : 0
% 1.80/1.19  #Close   : 0
% 1.80/1.19  
% 1.80/1.19  Ordering : KBO
% 1.80/1.19  
% 1.80/1.19  Simplification rules
% 1.80/1.19  ----------------------
% 1.80/1.19  #Subsume      : 5
% 1.80/1.19  #Demod        : 10
% 1.80/1.19  #Tautology    : 6
% 1.80/1.19  #SimpNegUnit  : 2
% 1.80/1.19  #BackRed      : 6
% 1.80/1.19  
% 1.80/1.19  #Partial instantiations: 0
% 1.80/1.19  #Strategies tried      : 1
% 1.80/1.19  
% 1.80/1.19  Timing (in seconds)
% 1.80/1.19  ----------------------
% 1.80/1.19  Preprocessing        : 0.27
% 1.80/1.19  Parsing              : 0.15
% 1.80/1.19  CNF conversion       : 0.02
% 1.80/1.19  Main loop            : 0.13
% 1.80/1.19  Inferencing          : 0.05
% 1.80/1.19  Reduction            : 0.04
% 1.80/1.19  Demodulation         : 0.02
% 1.80/1.19  BG Simplification    : 0.01
% 1.83/1.19  Subsumption          : 0.03
% 1.83/1.19  Abstraction          : 0.00
% 1.83/1.19  MUC search           : 0.00
% 1.83/1.19  Cooper               : 0.00
% 1.83/1.19  Total                : 0.43
% 1.83/1.19  Index Insertion      : 0.00
% 1.83/1.19  Index Deletion       : 0.00
% 1.83/1.19  Index Matching       : 0.00
% 1.83/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
