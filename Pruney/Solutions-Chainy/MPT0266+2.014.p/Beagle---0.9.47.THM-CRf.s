%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:28 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_44,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [D_16,B_12] : r2_hidden(D_16,k2_tarski(D_16,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    k3_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_92,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    ! [D_35,A_36,B_37] :
      ( r2_hidden(D_35,A_36)
      | ~ r2_hidden(D_35,k3_xboole_0(A_36,B_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_8])).

tff(c_150,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,'#skF_7')
      | ~ r2_hidden(D_38,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_137])).

tff(c_158,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:43:09 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.15  %$ r2_hidden > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.69/1.15  
% 1.69/1.15  %Foreground sorts:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Background operators:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Foreground operators:
% 1.69/1.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.69/1.15  tff('#skF_7', type, '#skF_7': $i).
% 1.69/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.69/1.15  tff('#skF_6', type, '#skF_6': $i).
% 1.69/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.69/1.15  
% 1.69/1.15  tff(f_55, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 1.69/1.15  tff(f_48, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.69/1.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.69/1.15  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.69/1.15  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.69/1.15  tff(c_44, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.69/1.15  tff(c_28, plain, (![D_16, B_12]: (r2_hidden(D_16, k2_tarski(D_16, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.69/1.15  tff(c_46, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.69/1.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.69/1.15  tff(c_113, plain, (k3_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_46, c_2])).
% 1.69/1.15  tff(c_92, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.15  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.15  tff(c_137, plain, (![D_35, A_36, B_37]: (r2_hidden(D_35, A_36) | ~r2_hidden(D_35, k3_xboole_0(A_36, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_8])).
% 1.69/1.15  tff(c_150, plain, (![D_38]: (r2_hidden(D_38, '#skF_7') | ~r2_hidden(D_38, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_113, c_137])).
% 1.69/1.15  tff(c_158, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_28, c_150])).
% 1.69/1.15  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_158])).
% 1.69/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  Inference rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Ref     : 0
% 1.69/1.15  #Sup     : 30
% 1.69/1.15  #Fact    : 0
% 1.69/1.15  #Define  : 0
% 1.69/1.15  #Split   : 0
% 1.69/1.15  #Chain   : 0
% 1.69/1.15  #Close   : 0
% 1.69/1.15  
% 1.69/1.15  Ordering : KBO
% 1.69/1.15  
% 1.69/1.15  Simplification rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Subsume      : 0
% 1.69/1.15  #Demod        : 3
% 1.69/1.15  #Tautology    : 20
% 1.69/1.15  #SimpNegUnit  : 1
% 1.69/1.15  #BackRed      : 0
% 1.69/1.15  
% 1.69/1.15  #Partial instantiations: 0
% 1.69/1.15  #Strategies tried      : 1
% 1.69/1.15  
% 1.69/1.15  Timing (in seconds)
% 1.69/1.15  ----------------------
% 1.88/1.16  Preprocessing        : 0.29
% 1.88/1.16  Parsing              : 0.14
% 1.88/1.16  CNF conversion       : 0.02
% 1.88/1.16  Main loop            : 0.13
% 1.88/1.16  Inferencing          : 0.04
% 1.88/1.16  Reduction            : 0.05
% 1.88/1.16  Demodulation         : 0.04
% 1.88/1.16  BG Simplification    : 0.01
% 1.88/1.16  Subsumption          : 0.03
% 1.88/1.16  Abstraction          : 0.01
% 1.88/1.16  MUC search           : 0.00
% 1.88/1.16  Cooper               : 0.00
% 1.88/1.16  Total                : 0.44
% 1.88/1.16  Index Insertion      : 0.00
% 1.88/1.16  Index Deletion       : 0.00
% 1.88/1.16  Index Matching       : 0.00
% 1.88/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
