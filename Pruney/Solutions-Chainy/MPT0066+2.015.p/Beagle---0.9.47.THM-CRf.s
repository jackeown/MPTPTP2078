%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:14 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   37 (  69 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 ( 127 expanded)
%              Number of equality atoms :   11 (  24 expanded)
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
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

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
    r2_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37,plain,(
    ! [A_11,C_12,B_13] :
      ( r2_xboole_0(A_11,C_12)
      | ~ r2_xboole_0(B_13,C_12)
      | ~ r2_xboole_0(A_11,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    ! [A_14] :
      ( r2_xboole_0(A_14,'#skF_3')
      | ~ r2_xboole_0(A_14,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_37])).

tff(c_50,plain,(
    ! [A_15] :
      ( r2_xboole_0(A_15,'#skF_3')
      | A_15 = '#skF_2'
      | ~ r1_tarski(A_15,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_58,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_10])).

tff(c_67,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_16])).

tff(c_71,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_20])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_71])).

tff(c_76,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_33])).

tff(c_80,plain,(
    r2_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r2_xboole_0(A_3,C_5)
      | ~ r2_xboole_0(B_4,C_5)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,(
    ! [A_19] :
      ( r2_xboole_0(A_19,'#skF_1')
      | ~ r2_xboole_0(A_19,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_80,c_8])).

tff(c_104,plain,(
    ! [A_20] :
      ( r2_xboole_0(A_20,'#skF_1')
      | A_20 = '#skF_2'
      | ~ r1_tarski(A_20,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_113,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_118,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_113])).

tff(c_122,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_80])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:39:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.14  
% 1.60/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.15  %$ r2_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.60/1.15  
% 1.60/1.15  %Foreground sorts:
% 1.60/1.15  
% 1.60/1.15  
% 1.60/1.15  %Background operators:
% 1.60/1.15  
% 1.60/1.15  
% 1.60/1.15  %Foreground operators:
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.15  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.15  
% 1.60/1.16  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.60/1.16  tff(f_45, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 1.60/1.16  tff(f_38, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_xboole_1)).
% 1.60/1.16  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.16  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.16  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.16  tff(c_21, plain, (![A_9, B_10]: (r2_xboole_0(A_9, B_10) | B_10=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.16  tff(c_10, plain, (~r2_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.16  tff(c_33, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_21, c_10])).
% 1.60/1.16  tff(c_36, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_33])).
% 1.60/1.16  tff(c_12, plain, (r2_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.16  tff(c_37, plain, (![A_11, C_12, B_13]: (r2_xboole_0(A_11, C_12) | ~r2_xboole_0(B_13, C_12) | ~r2_xboole_0(A_11, B_13))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.16  tff(c_44, plain, (![A_14]: (r2_xboole_0(A_14, '#skF_3') | ~r2_xboole_0(A_14, '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_37])).
% 1.60/1.16  tff(c_50, plain, (![A_15]: (r2_xboole_0(A_15, '#skF_3') | A_15='#skF_2' | ~r1_tarski(A_15, '#skF_2'))), inference(resolution, [status(thm)], [c_2, c_44])).
% 1.60/1.16  tff(c_58, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_10])).
% 1.60/1.16  tff(c_67, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_58])).
% 1.60/1.16  tff(c_16, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.16  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_16])).
% 1.60/1.16  tff(c_71, plain, (r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_20])).
% 1.60/1.16  tff(c_75, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_71])).
% 1.60/1.16  tff(c_76, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_33])).
% 1.60/1.16  tff(c_80, plain, (r2_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12])).
% 1.60/1.16  tff(c_8, plain, (![A_3, C_5, B_4]: (r2_xboole_0(A_3, C_5) | ~r2_xboole_0(B_4, C_5) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.16  tff(c_98, plain, (![A_19]: (r2_xboole_0(A_19, '#skF_1') | ~r2_xboole_0(A_19, '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_8])).
% 1.60/1.16  tff(c_104, plain, (![A_20]: (r2_xboole_0(A_20, '#skF_1') | A_20='#skF_2' | ~r1_tarski(A_20, '#skF_2'))), inference(resolution, [status(thm)], [c_2, c_98])).
% 1.60/1.16  tff(c_113, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_104, c_4])).
% 1.60/1.16  tff(c_118, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_113])).
% 1.60/1.16  tff(c_122, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_80])).
% 1.60/1.16  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_122])).
% 1.60/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  Inference rules
% 1.60/1.16  ----------------------
% 1.60/1.16  #Ref     : 0
% 1.60/1.16  #Sup     : 20
% 1.60/1.16  #Fact    : 0
% 1.60/1.16  #Define  : 0
% 1.60/1.16  #Split   : 1
% 1.60/1.16  #Chain   : 0
% 1.60/1.16  #Close   : 0
% 1.60/1.16  
% 1.60/1.16  Ordering : KBO
% 1.60/1.16  
% 1.60/1.16  Simplification rules
% 1.60/1.16  ----------------------
% 1.60/1.16  #Subsume      : 2
% 1.60/1.16  #Demod        : 20
% 1.60/1.16  #Tautology    : 7
% 1.60/1.16  #SimpNegUnit  : 2
% 1.60/1.16  #BackRed      : 12
% 1.60/1.16  
% 1.60/1.16  #Partial instantiations: 0
% 1.60/1.16  #Strategies tried      : 1
% 1.60/1.16  
% 1.60/1.16  Timing (in seconds)
% 1.60/1.16  ----------------------
% 1.60/1.16  Preprocessing        : 0.24
% 1.60/1.16  Parsing              : 0.13
% 1.60/1.16  CNF conversion       : 0.01
% 1.60/1.16  Main loop            : 0.14
% 1.60/1.16  Inferencing          : 0.06
% 1.60/1.16  Reduction            : 0.04
% 1.60/1.16  Demodulation         : 0.02
% 1.60/1.16  BG Simplification    : 0.01
% 1.60/1.16  Subsumption          : 0.03
% 1.60/1.16  Abstraction          : 0.01
% 1.60/1.16  MUC search           : 0.00
% 1.60/1.16  Cooper               : 0.00
% 1.60/1.16  Total                : 0.41
% 1.60/1.16  Index Insertion      : 0.00
% 1.60/1.16  Index Deletion       : 0.00
% 1.60/1.16  Index Matching       : 0.00
% 1.60/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
