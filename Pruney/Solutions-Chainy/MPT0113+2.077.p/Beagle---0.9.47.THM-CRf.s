%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:21 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  76 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_14,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_19,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_16,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [C_22,B_23,A_24] :
      ( r2_hidden(C_22,B_23)
      | ~ r2_hidden(C_22,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_37,B_38,B_39] :
      ( r2_hidden('#skF_1'(A_37,B_38),B_39)
      | ~ r1_tarski(A_37,B_39)
      | r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_154,plain,(
    ! [A_74,B_75,B_76,B_77] :
      ( r2_hidden('#skF_1'(A_74,B_75),B_76)
      | ~ r1_tarski(B_77,B_76)
      | ~ r1_tarski(A_74,B_77)
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_74,c_2])).

tff(c_164,plain,(
    ! [A_78,B_79,A_80,B_81] :
      ( r2_hidden('#skF_1'(A_78,B_79),A_80)
      | ~ r1_tarski(A_78,k4_xboole_0(A_80,B_81))
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_8,c_154])).

tff(c_176,plain,(
    ! [B_82] :
      ( r2_hidden('#skF_1'('#skF_2',B_82),'#skF_3')
      | r1_tarski('#skF_2',B_82) ) ),
    inference(resolution,[status(thm)],[c_16,c_164])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_182,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_4])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_19,c_182])).

tff(c_188,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_xboole_0(k4_xboole_0(A_11,B_12),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_202,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_xboole_0(A_91,C_92)
      | ~ r1_xboole_0(B_93,C_92)
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_206,plain,(
    ! [A_94,B_95,A_96] :
      ( r1_xboole_0(A_94,B_95)
      | ~ r1_tarski(A_94,k4_xboole_0(A_96,B_95)) ) ),
    inference(resolution,[status(thm)],[c_12,c_202])).

tff(c_217,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_206])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.81/1.19  
% 1.81/1.19  %Foreground sorts:
% 1.81/1.19  
% 1.81/1.19  
% 1.81/1.19  %Background operators:
% 1.81/1.19  
% 1.81/1.19  
% 1.81/1.19  %Foreground operators:
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.81/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.19  
% 1.81/1.20  tff(f_49, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.81/1.20  tff(f_34, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.81/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.81/1.20  tff(f_42, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.81/1.20  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.81/1.20  tff(c_14, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.20  tff(c_19, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_14])).
% 1.81/1.20  tff(c_16, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.20  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.81/1.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.20  tff(c_28, plain, (![C_22, B_23, A_24]: (r2_hidden(C_22, B_23) | ~r2_hidden(C_22, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.20  tff(c_74, plain, (![A_37, B_38, B_39]: (r2_hidden('#skF_1'(A_37, B_38), B_39) | ~r1_tarski(A_37, B_39) | r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_6, c_28])).
% 1.81/1.20  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.20  tff(c_154, plain, (![A_74, B_75, B_76, B_77]: (r2_hidden('#skF_1'(A_74, B_75), B_76) | ~r1_tarski(B_77, B_76) | ~r1_tarski(A_74, B_77) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_74, c_2])).
% 1.81/1.20  tff(c_164, plain, (![A_78, B_79, A_80, B_81]: (r2_hidden('#skF_1'(A_78, B_79), A_80) | ~r1_tarski(A_78, k4_xboole_0(A_80, B_81)) | r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_8, c_154])).
% 1.81/1.20  tff(c_176, plain, (![B_82]: (r2_hidden('#skF_1'('#skF_2', B_82), '#skF_3') | r1_tarski('#skF_2', B_82))), inference(resolution, [status(thm)], [c_16, c_164])).
% 1.81/1.20  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.20  tff(c_182, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_176, c_4])).
% 1.81/1.20  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19, c_19, c_182])).
% 1.81/1.20  tff(c_188, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_14])).
% 1.81/1.20  tff(c_12, plain, (![A_11, B_12]: (r1_xboole_0(k4_xboole_0(A_11, B_12), B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.20  tff(c_202, plain, (![A_91, C_92, B_93]: (r1_xboole_0(A_91, C_92) | ~r1_xboole_0(B_93, C_92) | ~r1_tarski(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.81/1.20  tff(c_206, plain, (![A_94, B_95, A_96]: (r1_xboole_0(A_94, B_95) | ~r1_tarski(A_94, k4_xboole_0(A_96, B_95)))), inference(resolution, [status(thm)], [c_12, c_202])).
% 1.81/1.20  tff(c_217, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_206])).
% 1.81/1.20  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_217])).
% 1.81/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  Inference rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Ref     : 0
% 1.81/1.20  #Sup     : 42
% 1.81/1.20  #Fact    : 0
% 1.81/1.20  #Define  : 0
% 1.81/1.20  #Split   : 1
% 1.81/1.20  #Chain   : 0
% 1.81/1.20  #Close   : 0
% 1.81/1.20  
% 1.81/1.20  Ordering : KBO
% 1.81/1.20  
% 1.81/1.20  Simplification rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Subsume      : 4
% 1.81/1.20  #Demod        : 6
% 1.81/1.20  #Tautology    : 7
% 1.81/1.20  #SimpNegUnit  : 2
% 1.81/1.20  #BackRed      : 0
% 1.81/1.20  
% 1.81/1.20  #Partial instantiations: 0
% 1.81/1.20  #Strategies tried      : 1
% 1.81/1.20  
% 1.81/1.20  Timing (in seconds)
% 1.81/1.20  ----------------------
% 1.81/1.21  Preprocessing        : 0.23
% 1.81/1.21  Parsing              : 0.13
% 1.81/1.21  CNF conversion       : 0.02
% 1.81/1.21  Main loop            : 0.21
% 1.81/1.21  Inferencing          : 0.08
% 1.81/1.21  Reduction            : 0.05
% 1.81/1.21  Demodulation         : 0.04
% 1.81/1.21  BG Simplification    : 0.01
% 1.81/1.21  Subsumption          : 0.05
% 1.81/1.21  Abstraction          : 0.01
% 1.81/1.21  MUC search           : 0.00
% 1.81/1.21  Cooper               : 0.00
% 1.81/1.21  Total                : 0.47
% 1.81/1.21  Index Insertion      : 0.00
% 1.81/1.21  Index Deletion       : 0.00
% 1.81/1.21  Index Matching       : 0.00
% 1.81/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
