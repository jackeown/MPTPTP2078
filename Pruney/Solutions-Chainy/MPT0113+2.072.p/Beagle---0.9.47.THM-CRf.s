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
% DateTime   : Thu Dec  3 09:45:20 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  70 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_32,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_117,plain,(
    ! [A_49,B_50,B_51] :
      ( r2_hidden('#skF_1'(A_49,B_50),B_51)
      | ~ r1_tarski(A_49,B_51)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_563,plain,(
    ! [A_168,B_169,A_170,B_171] :
      ( r2_hidden('#skF_1'(A_168,B_169),A_170)
      | ~ r1_tarski(A_168,k4_xboole_0(A_170,B_171))
      | r1_tarski(A_168,B_169) ) ),
    inference(resolution,[status(thm)],[c_117,c_12])).

tff(c_580,plain,(
    ! [B_172] :
      ( r2_hidden('#skF_1'('#skF_4',B_172),'#skF_5')
      | r1_tarski('#skF_4',B_172) ) ),
    inference(resolution,[status(thm)],[c_34,c_563])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_588,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_580,c_4])).

tff(c_594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_588])).

tff(c_595,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_630,plain,(
    ! [A_189,C_190,B_191] :
      ( r1_xboole_0(A_189,C_190)
      | ~ r1_xboole_0(B_191,C_190)
      | ~ r1_tarski(A_189,B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_634,plain,(
    ! [A_192,B_193,A_194] :
      ( r1_xboole_0(A_192,B_193)
      | ~ r1_tarski(A_192,k4_xboole_0(A_194,B_193)) ) ),
    inference(resolution,[status(thm)],[c_30,c_630])).

tff(c_641,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_634])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_641])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:47:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.47  
% 2.79/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.85/1.47  
% 2.85/1.47  %Foreground sorts:
% 2.85/1.47  
% 2.85/1.47  
% 2.85/1.47  %Background operators:
% 2.85/1.47  
% 2.85/1.47  
% 2.85/1.47  %Foreground operators:
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.85/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.85/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.85/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.85/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.85/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.47  
% 2.85/1.48  tff(f_59, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.85/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.85/1.48  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.85/1.48  tff(f_52, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.85/1.48  tff(f_50, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.85/1.48  tff(c_32, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.85/1.48  tff(c_36, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_32])).
% 2.85/1.48  tff(c_34, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.85/1.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.85/1.48  tff(c_88, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.85/1.48  tff(c_117, plain, (![A_49, B_50, B_51]: (r2_hidden('#skF_1'(A_49, B_50), B_51) | ~r1_tarski(A_49, B_51) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_6, c_88])).
% 2.85/1.48  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.85/1.48  tff(c_563, plain, (![A_168, B_169, A_170, B_171]: (r2_hidden('#skF_1'(A_168, B_169), A_170) | ~r1_tarski(A_168, k4_xboole_0(A_170, B_171)) | r1_tarski(A_168, B_169))), inference(resolution, [status(thm)], [c_117, c_12])).
% 2.85/1.48  tff(c_580, plain, (![B_172]: (r2_hidden('#skF_1'('#skF_4', B_172), '#skF_5') | r1_tarski('#skF_4', B_172))), inference(resolution, [status(thm)], [c_34, c_563])).
% 2.85/1.48  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.85/1.48  tff(c_588, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_580, c_4])).
% 2.85/1.48  tff(c_594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_588])).
% 2.85/1.48  tff(c_595, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 2.85/1.48  tff(c_30, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.85/1.48  tff(c_630, plain, (![A_189, C_190, B_191]: (r1_xboole_0(A_189, C_190) | ~r1_xboole_0(B_191, C_190) | ~r1_tarski(A_189, B_191))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.85/1.48  tff(c_634, plain, (![A_192, B_193, A_194]: (r1_xboole_0(A_192, B_193) | ~r1_tarski(A_192, k4_xboole_0(A_194, B_193)))), inference(resolution, [status(thm)], [c_30, c_630])).
% 2.85/1.48  tff(c_641, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_34, c_634])).
% 2.85/1.48  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_595, c_641])).
% 2.85/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.48  
% 2.85/1.48  Inference rules
% 2.85/1.48  ----------------------
% 2.85/1.48  #Ref     : 0
% 2.85/1.48  #Sup     : 126
% 2.85/1.48  #Fact    : 0
% 2.85/1.48  #Define  : 0
% 2.85/1.48  #Split   : 2
% 2.85/1.48  #Chain   : 0
% 2.85/1.48  #Close   : 0
% 2.85/1.48  
% 2.85/1.48  Ordering : KBO
% 2.85/1.48  
% 2.85/1.48  Simplification rules
% 2.85/1.48  ----------------------
% 2.85/1.48  #Subsume      : 8
% 2.85/1.48  #Demod        : 25
% 2.85/1.48  #Tautology    : 32
% 2.85/1.48  #SimpNegUnit  : 2
% 2.85/1.48  #BackRed      : 0
% 2.85/1.48  
% 2.85/1.48  #Partial instantiations: 0
% 2.85/1.48  #Strategies tried      : 1
% 2.85/1.48  
% 2.85/1.48  Timing (in seconds)
% 2.85/1.48  ----------------------
% 2.85/1.48  Preprocessing        : 0.31
% 2.85/1.48  Parsing              : 0.16
% 2.85/1.48  CNF conversion       : 0.03
% 2.85/1.48  Main loop            : 0.34
% 2.85/1.48  Inferencing          : 0.14
% 2.85/1.48  Reduction            : 0.08
% 2.85/1.48  Demodulation         : 0.06
% 2.85/1.48  BG Simplification    : 0.02
% 2.85/1.48  Subsumption          : 0.08
% 2.85/1.48  Abstraction          : 0.02
% 2.85/1.48  MUC search           : 0.00
% 2.85/1.48  Cooper               : 0.00
% 2.85/1.48  Total                : 0.68
% 2.85/1.48  Index Insertion      : 0.00
% 2.85/1.48  Index Deletion       : 0.00
% 2.85/1.48  Index Matching       : 0.00
% 2.85/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
