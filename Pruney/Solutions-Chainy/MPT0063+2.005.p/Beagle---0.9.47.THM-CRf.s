%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:09 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   30 (  44 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   37 (  71 expanded)
%              Number of equality atoms :    4 (   9 expanded)
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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r2_xboole_0(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(c_16,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    ! [A_13,B_14] :
      ( r2_xboole_0(A_13,B_14)
      | B_14 = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_59,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_12])).

tff(c_60,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ r2_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_18])).

tff(c_14,plain,(
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_25,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_18])).

tff(c_62,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_tarski(A_15,C_16)
      | ~ r1_tarski(B_17,C_16)
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,'#skF_3')
      | ~ r1_tarski(A_18,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_25,c_62])).

tff(c_73,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_70])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_73])).

tff(c_78,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_27,plain,(
    ! [B_11,A_12] :
      ( ~ r2_xboole_0(B_11,A_12)
      | ~ r2_xboole_0(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_32,plain,(
    ~ r2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_27])).

tff(c_80,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_32])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.10  
% 1.61/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.10  %$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.61/1.10  
% 1.61/1.10  %Foreground sorts:
% 1.61/1.10  
% 1.61/1.10  
% 1.61/1.10  %Background operators:
% 1.61/1.10  
% 1.61/1.10  
% 1.61/1.10  %Foreground operators:
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.10  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.10  
% 1.61/1.11  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_xboole_1)).
% 1.61/1.11  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.61/1.11  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.61/1.11  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.61/1.11  tff(c_16, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.61/1.11  tff(c_34, plain, (![A_13, B_14]: (r2_xboole_0(A_13, B_14) | B_14=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.61/1.11  tff(c_12, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.61/1.11  tff(c_59, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_12])).
% 1.61/1.11  tff(c_60, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_59])).
% 1.61/1.11  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~r2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.61/1.11  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_18])).
% 1.61/1.11  tff(c_14, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.61/1.11  tff(c_25, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_18])).
% 1.61/1.11  tff(c_62, plain, (![A_15, C_16, B_17]: (r1_tarski(A_15, C_16) | ~r1_tarski(B_17, C_16) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.61/1.11  tff(c_70, plain, (![A_18]: (r1_tarski(A_18, '#skF_3') | ~r1_tarski(A_18, '#skF_2'))), inference(resolution, [status(thm)], [c_25, c_62])).
% 1.61/1.11  tff(c_73, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_70])).
% 1.61/1.11  tff(c_77, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_73])).
% 1.61/1.11  tff(c_78, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_59])).
% 1.61/1.11  tff(c_27, plain, (![B_11, A_12]: (~r2_xboole_0(B_11, A_12) | ~r2_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.61/1.11  tff(c_32, plain, (~r2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_14, c_27])).
% 1.61/1.11  tff(c_80, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_32])).
% 1.61/1.11  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_80])).
% 1.61/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.11  
% 1.61/1.11  Inference rules
% 1.61/1.11  ----------------------
% 1.61/1.11  #Ref     : 0
% 1.61/1.11  #Sup     : 13
% 1.61/1.11  #Fact    : 0
% 1.61/1.11  #Define  : 0
% 1.61/1.11  #Split   : 3
% 1.61/1.11  #Chain   : 0
% 1.61/1.11  #Close   : 0
% 1.61/1.11  
% 1.61/1.11  Ordering : KBO
% 1.61/1.11  
% 1.61/1.11  Simplification rules
% 1.61/1.11  ----------------------
% 1.61/1.11  #Subsume      : 0
% 1.61/1.11  #Demod        : 5
% 1.61/1.11  #Tautology    : 2
% 1.61/1.11  #SimpNegUnit  : 1
% 1.61/1.11  #BackRed      : 4
% 1.61/1.11  
% 1.61/1.11  #Partial instantiations: 0
% 1.61/1.11  #Strategies tried      : 1
% 1.61/1.11  
% 1.61/1.11  Timing (in seconds)
% 1.61/1.11  ----------------------
% 1.61/1.11  Preprocessing        : 0.25
% 1.61/1.11  Parsing              : 0.14
% 1.61/1.11  CNF conversion       : 0.02
% 1.61/1.11  Main loop            : 0.12
% 1.61/1.11  Inferencing          : 0.05
% 1.61/1.11  Reduction            : 0.03
% 1.61/1.11  Demodulation         : 0.02
% 1.61/1.11  BG Simplification    : 0.01
% 1.61/1.11  Subsumption          : 0.02
% 1.61/1.11  Abstraction          : 0.00
% 1.61/1.11  MUC search           : 0.00
% 1.61/1.11  Cooper               : 0.00
% 1.61/1.11  Total                : 0.39
% 1.61/1.11  Index Insertion      : 0.00
% 1.61/1.11  Index Deletion       : 0.00
% 1.61/1.11  Index Matching       : 0.00
% 1.61/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
