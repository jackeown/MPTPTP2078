%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:29 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  22 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( ~ r2_hidden(D_11,A_6)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden('#skF_1'(A_20,B_21),B_21)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_229,plain,(
    ! [A_65,A_66,B_67] :
      ( r1_tarski(A_65,k2_xboole_0(A_66,B_67))
      | ~ r2_hidden('#skF_1'(A_65,k2_xboole_0(A_66,B_67)),A_66) ) ),
    inference(resolution,[status(thm)],[c_12,c_30])).

tff(c_257,plain,(
    ! [A_1,B_67] : r1_tarski(A_1,k2_xboole_0(A_1,B_67)) ),
    inference(resolution,[status(thm)],[c_6,c_229])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.23  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.00/1.23  
% 2.00/1.23  %Foreground sorts:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Background operators:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Foreground operators:
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.00/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.23  
% 2.05/1.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.05/1.24  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.05/1.24  tff(f_44, negated_conjecture, ~(![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.05/1.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.24  tff(c_12, plain, (![D_11, A_6, B_7]: (~r2_hidden(D_11, A_6) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.24  tff(c_30, plain, (![A_20, B_21]: (~r2_hidden('#skF_1'(A_20, B_21), B_21) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.05/1.24  tff(c_229, plain, (![A_65, A_66, B_67]: (r1_tarski(A_65, k2_xboole_0(A_66, B_67)) | ~r2_hidden('#skF_1'(A_65, k2_xboole_0(A_66, B_67)), A_66))), inference(resolution, [status(thm)], [c_12, c_30])).
% 2.05/1.24  tff(c_257, plain, (![A_1, B_67]: (r1_tarski(A_1, k2_xboole_0(A_1, B_67)))), inference(resolution, [status(thm)], [c_6, c_229])).
% 2.05/1.24  tff(c_26, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.05/1.24  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_257, c_26])).
% 2.05/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  Inference rules
% 2.05/1.24  ----------------------
% 2.05/1.24  #Ref     : 0
% 2.05/1.24  #Sup     : 49
% 2.05/1.24  #Fact    : 0
% 2.05/1.24  #Define  : 0
% 2.05/1.24  #Split   : 0
% 2.05/1.24  #Chain   : 0
% 2.05/1.24  #Close   : 0
% 2.05/1.24  
% 2.05/1.24  Ordering : KBO
% 2.05/1.24  
% 2.05/1.24  Simplification rules
% 2.05/1.24  ----------------------
% 2.05/1.24  #Subsume      : 4
% 2.05/1.24  #Demod        : 1
% 2.05/1.24  #Tautology    : 3
% 2.05/1.24  #SimpNegUnit  : 0
% 2.05/1.24  #BackRed      : 1
% 2.05/1.24  
% 2.05/1.24  #Partial instantiations: 0
% 2.05/1.24  #Strategies tried      : 1
% 2.05/1.24  
% 2.05/1.24  Timing (in seconds)
% 2.05/1.24  ----------------------
% 2.05/1.24  Preprocessing        : 0.26
% 2.05/1.24  Parsing              : 0.14
% 2.05/1.24  CNF conversion       : 0.02
% 2.05/1.24  Main loop            : 0.20
% 2.05/1.24  Inferencing          : 0.09
% 2.05/1.24  Reduction            : 0.04
% 2.05/1.24  Demodulation         : 0.03
% 2.05/1.24  BG Simplification    : 0.02
% 2.05/1.24  Subsumption          : 0.05
% 2.05/1.24  Abstraction          : 0.01
% 2.05/1.24  MUC search           : 0.00
% 2.05/1.24  Cooper               : 0.00
% 2.05/1.24  Total                : 0.48
% 2.05/1.24  Index Insertion      : 0.00
% 2.05/1.24  Index Deletion       : 0.00
% 2.05/1.24  Index Matching       : 0.00
% 2.05/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
