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
% DateTime   : Thu Dec  3 09:43:11 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   34 (  51 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  83 expanded)
%              Number of equality atoms :    6 (  13 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_xboole_0(A,B)
          & r1_tarski(B,C) )
       => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_47,axiom,(
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

tff(c_6,plain,(
    ! [B_4] : ~ r2_xboole_0(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_21,B_22] :
      ( r2_xboole_0(A_21,B_22)
      | B_22 = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_80,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_16])).

tff(c_83,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_20,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_27,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r2_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_27])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_84,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,C_24)
      | ~ r1_tarski(B_25,C_24)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_95,plain,(
    ! [A_26] :
      ( r1_tarski(A_26,'#skF_3')
      | ~ r1_tarski(A_26,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_84])).

tff(c_98,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_31,c_95])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_98])).

tff(c_103,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_107,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_18])).

tff(c_23,plain,(
    ! [B_15,A_16] :
      ( ~ r2_xboole_0(B_15,A_16)
      | ~ r2_xboole_0(A_16,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_26,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_23])).

tff(c_78,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_61,c_26])).

tff(c_152,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_78])).

tff(c_158,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_20])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.25  
% 1.88/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.26  %$ r2_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.88/1.26  
% 1.88/1.26  %Foreground sorts:
% 1.88/1.26  
% 1.88/1.26  
% 1.88/1.26  %Background operators:
% 1.88/1.26  
% 1.88/1.26  
% 1.88/1.26  %Foreground operators:
% 1.88/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.26  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.88/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.26  
% 1.88/1.27  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.88/1.27  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.88/1.27  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.88/1.27  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 1.88/1.27  tff(c_6, plain, (![B_4]: (~r2_xboole_0(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.27  tff(c_61, plain, (![A_21, B_22]: (r2_xboole_0(A_21, B_22) | B_22=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.27  tff(c_16, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.27  tff(c_80, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_61, c_16])).
% 1.88/1.27  tff(c_83, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_80])).
% 1.88/1.27  tff(c_20, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.27  tff(c_27, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.27  tff(c_31, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_27])).
% 1.88/1.27  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.27  tff(c_84, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, C_24) | ~r1_tarski(B_25, C_24) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.27  tff(c_95, plain, (![A_26]: (r1_tarski(A_26, '#skF_3') | ~r1_tarski(A_26, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_84])).
% 1.88/1.27  tff(c_98, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_31, c_95])).
% 1.88/1.27  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_98])).
% 1.88/1.27  tff(c_103, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_80])).
% 1.88/1.27  tff(c_107, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_18])).
% 1.88/1.27  tff(c_23, plain, (![B_15, A_16]: (~r2_xboole_0(B_15, A_16) | ~r2_xboole_0(A_16, B_15))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.88/1.27  tff(c_26, plain, (~r2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_23])).
% 1.88/1.27  tff(c_78, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_61, c_26])).
% 1.88/1.27  tff(c_152, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_78])).
% 1.88/1.27  tff(c_158, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_20])).
% 1.88/1.27  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_158])).
% 1.88/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.27  
% 1.88/1.27  Inference rules
% 1.88/1.27  ----------------------
% 1.88/1.27  #Ref     : 0
% 1.88/1.27  #Sup     : 34
% 1.88/1.27  #Fact    : 0
% 1.88/1.27  #Define  : 0
% 1.88/1.27  #Split   : 2
% 1.88/1.27  #Chain   : 0
% 1.88/1.27  #Close   : 0
% 1.88/1.27  
% 1.88/1.27  Ordering : KBO
% 1.88/1.27  
% 1.88/1.27  Simplification rules
% 1.88/1.27  ----------------------
% 1.88/1.27  #Subsume      : 2
% 1.88/1.27  #Demod        : 22
% 1.88/1.27  #Tautology    : 22
% 1.88/1.27  #SimpNegUnit  : 2
% 1.88/1.27  #BackRed      : 9
% 1.88/1.27  
% 1.88/1.27  #Partial instantiations: 0
% 1.88/1.27  #Strategies tried      : 1
% 1.88/1.27  
% 1.88/1.27  Timing (in seconds)
% 1.88/1.27  ----------------------
% 1.88/1.27  Preprocessing        : 0.27
% 1.88/1.27  Parsing              : 0.16
% 1.88/1.27  CNF conversion       : 0.02
% 1.88/1.27  Main loop            : 0.14
% 1.88/1.27  Inferencing          : 0.05
% 1.88/1.27  Reduction            : 0.04
% 1.88/1.27  Demodulation         : 0.03
% 1.88/1.27  BG Simplification    : 0.01
% 1.88/1.27  Subsumption          : 0.02
% 1.88/1.27  Abstraction          : 0.01
% 1.88/1.27  MUC search           : 0.00
% 1.88/1.27  Cooper               : 0.00
% 1.88/1.27  Total                : 0.44
% 1.88/1.27  Index Insertion      : 0.00
% 1.88/1.27  Index Deletion       : 0.00
% 1.88/1.27  Index Matching       : 0.00
% 1.88/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
