%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:55 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   40 (  51 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  43 expanded)
%              Number of equality atoms :   11 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_22,plain,(
    ! [D_19,B_15] : r2_hidden(D_19,k2_tarski(D_19,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_92,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_22])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_235,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,B_60)
      | ~ r2_hidden(C_61,A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_239,plain,(
    ! [C_62,A_63] :
      ( ~ r2_hidden(C_62,k1_xboole_0)
      | ~ r2_hidden(C_62,A_63) ) ),
    inference(resolution,[status(thm)],[c_14,c_235])).

tff(c_253,plain,(
    ! [A_63] : ~ r2_hidden('#skF_4',A_63) ),
    inference(resolution,[status(thm)],[c_92,c_239])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n018.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:30:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.33  
% 2.19/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.34  %$ r2_hidden > r1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.19/1.34  
% 2.19/1.34  %Foreground sorts:
% 2.19/1.34  
% 2.19/1.34  
% 2.19/1.34  %Background operators:
% 2.19/1.34  
% 2.19/1.34  
% 2.19/1.34  %Foreground operators:
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.34  
% 2.19/1.35  tff(f_76, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.19/1.35  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.19/1.35  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.19/1.35  tff(f_62, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.19/1.35  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.19/1.35  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.19/1.35  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.35  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.35  tff(c_69, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_46, c_12])).
% 2.19/1.35  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.19/1.35  tff(c_76, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_69, c_10])).
% 2.19/1.35  tff(c_22, plain, (![D_19, B_15]: (r2_hidden(D_19, k2_tarski(D_19, B_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.35  tff(c_92, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_76, c_22])).
% 2.19/1.35  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.35  tff(c_235, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, B_60) | ~r2_hidden(C_61, A_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.35  tff(c_239, plain, (![C_62, A_63]: (~r2_hidden(C_62, k1_xboole_0) | ~r2_hidden(C_62, A_63))), inference(resolution, [status(thm)], [c_14, c_235])).
% 2.19/1.35  tff(c_253, plain, (![A_63]: (~r2_hidden('#skF_4', A_63))), inference(resolution, [status(thm)], [c_92, c_239])).
% 2.19/1.35  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_253, c_92])).
% 2.19/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.35  
% 2.19/1.35  Inference rules
% 2.19/1.35  ----------------------
% 2.19/1.35  #Ref     : 0
% 2.19/1.35  #Sup     : 58
% 2.19/1.35  #Fact    : 0
% 2.19/1.35  #Define  : 0
% 2.19/1.35  #Split   : 0
% 2.19/1.35  #Chain   : 0
% 2.19/1.35  #Close   : 0
% 2.19/1.35  
% 2.19/1.35  Ordering : KBO
% 2.19/1.35  
% 2.19/1.35  Simplification rules
% 2.19/1.35  ----------------------
% 2.19/1.35  #Subsume      : 0
% 2.19/1.35  #Demod        : 13
% 2.19/1.35  #Tautology    : 43
% 2.19/1.35  #SimpNegUnit  : 1
% 2.19/1.35  #BackRed      : 3
% 2.19/1.35  
% 2.19/1.35  #Partial instantiations: 0
% 2.19/1.35  #Strategies tried      : 1
% 2.19/1.35  
% 2.19/1.35  Timing (in seconds)
% 2.19/1.35  ----------------------
% 2.19/1.35  Preprocessing        : 0.31
% 2.19/1.35  Parsing              : 0.16
% 2.19/1.35  CNF conversion       : 0.02
% 2.19/1.35  Main loop            : 0.16
% 2.19/1.35  Inferencing          : 0.06
% 2.19/1.35  Reduction            : 0.05
% 2.19/1.35  Demodulation         : 0.04
% 2.19/1.35  BG Simplification    : 0.01
% 2.19/1.35  Subsumption          : 0.02
% 2.19/1.35  Abstraction          : 0.01
% 2.19/1.35  MUC search           : 0.00
% 2.19/1.35  Cooper               : 0.00
% 2.19/1.35  Total                : 0.50
% 2.19/1.35  Index Insertion      : 0.00
% 2.19/1.35  Index Deletion       : 0.00
% 2.19/1.35  Index Matching       : 0.00
% 2.19/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
