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
% DateTime   : Thu Dec  3 09:43:13 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   36 (  57 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  95 expanded)
%              Number of equality atoms :    7 (  16 expanded)
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

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

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

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_xboole_0(A_3,B_4)
      | B_4 = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

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

tff(c_16,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_24])).

tff(c_69,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,C_22)
      | ~ r1_tarski(B_23,C_22)
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    ! [A_25] :
      ( r1_tarski(A_25,'#skF_3')
      | ~ r1_tarski(A_25,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_69])).

tff(c_94,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_88])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_94])).

tff(c_100,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_20,plain,(
    ! [B_11,A_12] :
      ( ~ r2_xboole_0(B_11,A_12)
      | ~ r2_xboole_0(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_23,plain,(
    ~ r2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_20])).

tff(c_103,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_23])).

tff(c_130,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_103])).

tff(c_133,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_130])).

tff(c_105,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_16])).

tff(c_136,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_105])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.29  % Computer   : n001.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % DateTime   : Tue Dec  1 15:35:15 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.10/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.10  
% 1.71/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.10  %$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.71/1.10  
% 1.71/1.10  %Foreground sorts:
% 1.71/1.10  
% 1.71/1.10  
% 1.71/1.10  %Background operators:
% 1.71/1.10  
% 1.71/1.10  
% 1.71/1.10  %Foreground operators:
% 1.71/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.10  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.71/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.10  
% 1.71/1.12  tff(f_40, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 1.71/1.12  tff(f_53, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_xboole_1)).
% 1.71/1.12  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.71/1.12  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.71/1.12  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.71/1.12  tff(c_10, plain, (![A_5]: (~r2_xboole_0(A_5, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.71/1.12  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.71/1.12  tff(c_4, plain, (![A_3, B_4]: (r2_xboole_0(A_3, B_4) | B_4=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.12  tff(c_29, plain, (![A_15, B_16]: (r2_xboole_0(A_15, B_16) | B_16=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.12  tff(c_14, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.71/1.12  tff(c_48, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_29, c_14])).
% 1.71/1.12  tff(c_51, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 1.71/1.12  tff(c_16, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.71/1.12  tff(c_24, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.71/1.12  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_24])).
% 1.71/1.12  tff(c_69, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, C_22) | ~r1_tarski(B_23, C_22) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.71/1.12  tff(c_88, plain, (![A_25]: (r1_tarski(A_25, '#skF_3') | ~r1_tarski(A_25, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_69])).
% 1.71/1.12  tff(c_94, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_88])).
% 1.71/1.12  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_94])).
% 1.71/1.12  tff(c_100, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_48])).
% 1.71/1.12  tff(c_20, plain, (![B_11, A_12]: (~r2_xboole_0(B_11, A_12) | ~r2_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.71/1.12  tff(c_23, plain, (~r2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_20])).
% 1.71/1.12  tff(c_103, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_23])).
% 1.71/1.12  tff(c_130, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4, c_103])).
% 1.71/1.12  tff(c_133, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_130])).
% 1.71/1.12  tff(c_105, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_16])).
% 1.71/1.12  tff(c_136, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_105])).
% 1.71/1.12  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_136])).
% 1.71/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.12  
% 1.71/1.12  Inference rules
% 1.71/1.12  ----------------------
% 1.71/1.12  #Ref     : 0
% 1.71/1.12  #Sup     : 26
% 1.71/1.12  #Fact    : 0
% 1.71/1.12  #Define  : 0
% 1.71/1.12  #Split   : 3
% 1.71/1.12  #Chain   : 0
% 1.71/1.12  #Close   : 0
% 1.71/1.12  
% 1.71/1.12  Ordering : KBO
% 1.71/1.12  
% 1.71/1.12  Simplification rules
% 1.71/1.12  ----------------------
% 1.71/1.12  #Subsume      : 5
% 1.71/1.12  #Demod        : 11
% 1.71/1.12  #Tautology    : 6
% 1.71/1.12  #SimpNegUnit  : 2
% 1.71/1.12  #BackRed      : 8
% 1.71/1.12  
% 1.71/1.12  #Partial instantiations: 0
% 1.71/1.12  #Strategies tried      : 1
% 1.71/1.12  
% 1.71/1.12  Timing (in seconds)
% 1.71/1.12  ----------------------
% 1.71/1.12  Preprocessing        : 0.25
% 1.71/1.12  Parsing              : 0.14
% 1.71/1.12  CNF conversion       : 0.02
% 1.71/1.12  Main loop            : 0.15
% 1.71/1.12  Inferencing          : 0.06
% 1.71/1.12  Reduction            : 0.04
% 1.71/1.12  Demodulation         : 0.02
% 1.71/1.12  BG Simplification    : 0.01
% 1.71/1.12  Subsumption          : 0.03
% 1.71/1.12  Abstraction          : 0.01
% 1.71/1.12  MUC search           : 0.00
% 1.71/1.12  Cooper               : 0.00
% 1.71/1.12  Total                : 0.43
% 1.71/1.12  Index Insertion      : 0.00
% 1.71/1.12  Index Deletion       : 0.00
% 1.71/1.12  Index Matching       : 0.00
% 1.71/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
