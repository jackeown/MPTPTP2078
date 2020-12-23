%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:46 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   27 (  30 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

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

tff(c_28,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    r1_tarski('#skF_5',k4_xboole_0('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    ! [C_26,B_27,A_28] :
      ( r2_hidden(C_26,B_27)
      | ~ r2_hidden(C_26,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_4'(A_32),B_33)
      | ~ r1_tarski(A_32,B_33)
      | k1_xboole_0 = A_32 ) ),
    inference(resolution,[status(thm)],[c_26,c_62])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_558,plain,(
    ! [A_84,B_85,A_86] :
      ( ~ r2_hidden('#skF_4'(A_84),B_85)
      | ~ r1_tarski(A_84,k4_xboole_0(A_86,B_85))
      | k1_xboole_0 = A_84 ) ),
    inference(resolution,[status(thm)],[c_86,c_10])).

tff(c_572,plain,(
    ! [A_87,A_88] :
      ( ~ r1_tarski(A_87,k4_xboole_0(A_88,A_87))
      | k1_xboole_0 = A_87 ) ),
    inference(resolution,[status(thm)],[c_26,c_558])).

tff(c_585,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_30,c_572])).

tff(c_591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_585])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:45:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.76  
% 2.63/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.76  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 2.63/1.76  
% 2.63/1.76  %Foreground sorts:
% 2.63/1.76  
% 2.63/1.76  
% 2.63/1.76  %Background operators:
% 2.63/1.76  
% 2.63/1.76  
% 2.63/1.76  %Foreground operators:
% 2.63/1.76  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.63/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.76  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.76  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.63/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.63/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.76  
% 2.63/1.77  tff(f_55, negated_conjecture, ~(![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.63/1.77  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.63/1.77  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.63/1.77  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.63/1.77  tff(c_28, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.77  tff(c_30, plain, (r1_tarski('#skF_5', k4_xboole_0('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.77  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.63/1.77  tff(c_62, plain, (![C_26, B_27, A_28]: (r2_hidden(C_26, B_27) | ~r2_hidden(C_26, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.77  tff(c_86, plain, (![A_32, B_33]: (r2_hidden('#skF_4'(A_32), B_33) | ~r1_tarski(A_32, B_33) | k1_xboole_0=A_32)), inference(resolution, [status(thm)], [c_26, c_62])).
% 2.63/1.77  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.63/1.77  tff(c_558, plain, (![A_84, B_85, A_86]: (~r2_hidden('#skF_4'(A_84), B_85) | ~r1_tarski(A_84, k4_xboole_0(A_86, B_85)) | k1_xboole_0=A_84)), inference(resolution, [status(thm)], [c_86, c_10])).
% 2.63/1.77  tff(c_572, plain, (![A_87, A_88]: (~r1_tarski(A_87, k4_xboole_0(A_88, A_87)) | k1_xboole_0=A_87)), inference(resolution, [status(thm)], [c_26, c_558])).
% 2.63/1.77  tff(c_585, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_30, c_572])).
% 2.63/1.77  tff(c_591, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_585])).
% 2.63/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.77  
% 2.63/1.77  Inference rules
% 2.63/1.77  ----------------------
% 2.63/1.77  #Ref     : 0
% 2.63/1.77  #Sup     : 120
% 2.63/1.77  #Fact    : 0
% 2.63/1.77  #Define  : 0
% 2.63/1.77  #Split   : 0
% 2.63/1.77  #Chain   : 0
% 2.63/1.77  #Close   : 0
% 2.63/1.77  
% 2.63/1.77  Ordering : KBO
% 2.63/1.77  
% 2.63/1.77  Simplification rules
% 2.63/1.77  ----------------------
% 2.63/1.77  #Subsume      : 17
% 2.63/1.77  #Demod        : 26
% 2.63/1.77  #Tautology    : 36
% 2.63/1.77  #SimpNegUnit  : 1
% 2.63/1.77  #BackRed      : 0
% 2.63/1.77  
% 2.63/1.77  #Partial instantiations: 0
% 2.63/1.77  #Strategies tried      : 1
% 2.63/1.77  
% 2.63/1.77  Timing (in seconds)
% 2.63/1.77  ----------------------
% 2.97/1.77  Preprocessing        : 0.43
% 2.97/1.77  Parsing              : 0.21
% 2.97/1.77  CNF conversion       : 0.04
% 2.97/1.78  Main loop            : 0.43
% 2.97/1.78  Inferencing          : 0.17
% 2.97/1.78  Reduction            : 0.10
% 2.97/1.78  Demodulation         : 0.07
% 2.97/1.78  BG Simplification    : 0.03
% 2.97/1.78  Subsumption          : 0.10
% 2.97/1.78  Abstraction          : 0.02
% 2.97/1.78  MUC search           : 0.00
% 2.97/1.78  Cooper               : 0.00
% 2.97/1.78  Total                : 0.90
% 2.97/1.78  Index Insertion      : 0.00
% 2.97/1.78  Index Deletion       : 0.00
% 2.97/1.78  Index Matching       : 0.00
% 2.97/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
