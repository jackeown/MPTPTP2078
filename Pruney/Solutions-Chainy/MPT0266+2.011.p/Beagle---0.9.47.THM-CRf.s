%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:27 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  32 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_52,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_91,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [E_17,A_11,C_13] : r2_hidden(E_17,k1_enumset1(A_11,E_17,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_100,plain,(
    ! [A_34,B_35] : r2_hidden(A_34,k2_tarski(A_34,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_28])).

tff(c_54,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_115,plain,(
    k3_xboole_0('#skF_7',k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_22,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [D_45,A_46,B_47] :
      ( r2_hidden(D_45,A_46)
      | ~ r2_hidden(D_45,k4_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_166,plain,(
    ! [D_51,A_52,B_53] :
      ( r2_hidden(D_51,A_52)
      | ~ r2_hidden(D_51,k3_xboole_0(A_52,B_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_147])).

tff(c_180,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,'#skF_7')
      | ~ r2_hidden(D_54,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_166])).

tff(c_184,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_100,c_180])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.25  
% 1.97/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.97/1.25  
% 1.97/1.25  %Foreground sorts:
% 1.97/1.25  
% 1.97/1.25  
% 1.97/1.25  %Background operators:
% 1.97/1.25  
% 1.97/1.25  
% 1.97/1.25  %Foreground operators:
% 1.97/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.25  tff('#skF_7', type, '#skF_7': $i).
% 1.97/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.25  tff('#skF_6', type, '#skF_6': $i).
% 1.97/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.97/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.97/1.25  
% 1.97/1.26  tff(f_63, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 1.97/1.26  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.97/1.26  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.97/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.97/1.26  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.97/1.26  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.97/1.26  tff(c_52, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.97/1.26  tff(c_91, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.26  tff(c_28, plain, (![E_17, A_11, C_13]: (r2_hidden(E_17, k1_enumset1(A_11, E_17, C_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.97/1.26  tff(c_100, plain, (![A_34, B_35]: (r2_hidden(A_34, k2_tarski(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_28])).
% 1.97/1.26  tff(c_54, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.97/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.26  tff(c_115, plain, (k3_xboole_0('#skF_7', k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 1.97/1.26  tff(c_22, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.26  tff(c_147, plain, (![D_45, A_46, B_47]: (r2_hidden(D_45, A_46) | ~r2_hidden(D_45, k4_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.26  tff(c_166, plain, (![D_51, A_52, B_53]: (r2_hidden(D_51, A_52) | ~r2_hidden(D_51, k3_xboole_0(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_147])).
% 1.97/1.26  tff(c_180, plain, (![D_54]: (r2_hidden(D_54, '#skF_7') | ~r2_hidden(D_54, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_115, c_166])).
% 1.97/1.26  tff(c_184, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_100, c_180])).
% 1.97/1.26  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_184])).
% 1.97/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.26  
% 1.97/1.26  Inference rules
% 1.97/1.26  ----------------------
% 1.97/1.26  #Ref     : 0
% 1.97/1.26  #Sup     : 35
% 1.97/1.26  #Fact    : 0
% 1.97/1.26  #Define  : 0
% 1.97/1.26  #Split   : 0
% 1.97/1.26  #Chain   : 0
% 1.97/1.26  #Close   : 0
% 1.97/1.26  
% 1.97/1.26  Ordering : KBO
% 1.97/1.26  
% 1.97/1.26  Simplification rules
% 1.97/1.26  ----------------------
% 1.97/1.26  #Subsume      : 0
% 1.97/1.26  #Demod        : 4
% 1.97/1.26  #Tautology    : 23
% 1.97/1.26  #SimpNegUnit  : 1
% 1.97/1.26  #BackRed      : 0
% 1.97/1.26  
% 1.97/1.26  #Partial instantiations: 0
% 1.97/1.26  #Strategies tried      : 1
% 1.97/1.26  
% 1.97/1.26  Timing (in seconds)
% 1.97/1.26  ----------------------
% 1.97/1.26  Preprocessing        : 0.31
% 1.97/1.26  Parsing              : 0.16
% 1.97/1.26  CNF conversion       : 0.02
% 1.97/1.26  Main loop            : 0.15
% 1.97/1.26  Inferencing          : 0.04
% 1.97/1.26  Reduction            : 0.06
% 1.97/1.26  Demodulation         : 0.04
% 1.97/1.26  BG Simplification    : 0.01
% 1.97/1.26  Subsumption          : 0.03
% 1.97/1.26  Abstraction          : 0.01
% 1.97/1.26  MUC search           : 0.00
% 1.97/1.26  Cooper               : 0.00
% 1.97/1.26  Total                : 0.48
% 1.97/1.26  Index Insertion      : 0.00
% 1.97/1.26  Index Deletion       : 0.00
% 1.97/1.26  Index Matching       : 0.00
% 1.97/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
