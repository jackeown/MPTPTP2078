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
% DateTime   : Thu Dec  3 09:50:37 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  36 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_36,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_39,plain,(
    r1_tarski(k2_xboole_0('#skF_5',k1_tarski('#skF_4')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38])).

tff(c_136,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(k2_xboole_0(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1358,plain,(
    ! [B_1456,C_1457,A_1458] :
      ( r1_tarski(B_1456,C_1457)
      | ~ r1_tarski(k2_xboole_0(A_1458,B_1456),C_1457) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_1442,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_39,c_1358])).

tff(c_30,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    ! [D_23,A_24] : r2_hidden(D_23,k2_tarski(A_24,D_23)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_49])).

tff(c_219,plain,(
    ! [C_51,B_52,A_53] :
      ( r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_230,plain,(
    ! [A_17,B_52] :
      ( r2_hidden(A_17,B_52)
      | ~ r1_tarski(k1_tarski(A_17),B_52) ) ),
    inference(resolution,[status(thm)],[c_52,c_219])).

tff(c_1445,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1442,c_230])).

tff(c_1449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:11:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.50  
% 2.97/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.50  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.97/1.50  
% 2.97/1.50  %Foreground sorts:
% 2.97/1.50  
% 2.97/1.50  
% 2.97/1.50  %Background operators:
% 2.97/1.50  
% 2.97/1.50  
% 2.97/1.50  %Foreground operators:
% 2.97/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.97/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.97/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.97/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.97/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.97/1.50  
% 2.97/1.51  tff(f_58, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.97/1.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.97/1.51  tff(f_38, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.97/1.51  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.97/1.51  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.97/1.51  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.97/1.51  tff(c_36, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.97/1.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.97/1.51  tff(c_38, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.97/1.51  tff(c_39, plain, (r1_tarski(k2_xboole_0('#skF_5', k1_tarski('#skF_4')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_38])).
% 2.97/1.51  tff(c_136, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(k2_xboole_0(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.97/1.51  tff(c_1358, plain, (![B_1456, C_1457, A_1458]: (r1_tarski(B_1456, C_1457) | ~r1_tarski(k2_xboole_0(A_1458, B_1456), C_1457))), inference(superposition, [status(thm), theory('equality')], [c_2, c_136])).
% 2.97/1.51  tff(c_1442, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_39, c_1358])).
% 2.97/1.51  tff(c_30, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.51  tff(c_49, plain, (![D_23, A_24]: (r2_hidden(D_23, k2_tarski(A_24, D_23)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.97/1.51  tff(c_52, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_49])).
% 2.97/1.51  tff(c_219, plain, (![C_51, B_52, A_53]: (r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.97/1.51  tff(c_230, plain, (![A_17, B_52]: (r2_hidden(A_17, B_52) | ~r1_tarski(k1_tarski(A_17), B_52))), inference(resolution, [status(thm)], [c_52, c_219])).
% 2.97/1.51  tff(c_1445, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1442, c_230])).
% 2.97/1.51  tff(c_1449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1445])).
% 2.97/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.51  
% 2.97/1.51  Inference rules
% 2.97/1.51  ----------------------
% 2.97/1.51  #Ref     : 0
% 2.97/1.51  #Sup     : 203
% 2.97/1.51  #Fact    : 4
% 2.97/1.51  #Define  : 0
% 2.97/1.51  #Split   : 0
% 2.97/1.51  #Chain   : 0
% 2.97/1.51  #Close   : 0
% 2.97/1.51  
% 2.97/1.51  Ordering : KBO
% 2.97/1.51  
% 2.97/1.51  Simplification rules
% 2.97/1.51  ----------------------
% 2.97/1.51  #Subsume      : 16
% 2.97/1.51  #Demod        : 53
% 2.97/1.51  #Tautology    : 78
% 2.97/1.51  #SimpNegUnit  : 1
% 2.97/1.51  #BackRed      : 0
% 2.97/1.51  
% 2.97/1.51  #Partial instantiations: 820
% 2.97/1.51  #Strategies tried      : 1
% 2.97/1.51  
% 2.97/1.51  Timing (in seconds)
% 2.97/1.51  ----------------------
% 2.97/1.51  Preprocessing        : 0.31
% 2.97/1.51  Parsing              : 0.16
% 2.97/1.51  CNF conversion       : 0.02
% 2.97/1.51  Main loop            : 0.43
% 2.97/1.51  Inferencing          : 0.21
% 2.97/1.51  Reduction            : 0.12
% 2.97/1.51  Demodulation         : 0.09
% 2.97/1.51  BG Simplification    : 0.02
% 2.97/1.51  Subsumption          : 0.06
% 2.97/1.51  Abstraction          : 0.02
% 2.97/1.51  MUC search           : 0.00
% 2.97/1.51  Cooper               : 0.00
% 2.97/1.51  Total                : 0.76
% 2.97/1.51  Index Insertion      : 0.00
% 2.97/1.51  Index Deletion       : 0.00
% 2.97/1.51  Index Matching       : 0.00
% 2.97/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
