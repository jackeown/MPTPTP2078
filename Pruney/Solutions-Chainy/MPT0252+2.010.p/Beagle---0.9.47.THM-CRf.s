%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:02 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  44 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_52,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [D_18,A_13] : r2_hidden(D_18,k2_tarski(A_13,D_18)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    ! [A_32,B_33] : k3_tarski(k2_tarski(A_32,B_33)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    ! [B_38,A_39] : k3_tarski(k2_tarski(B_38,A_39)) = k2_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_110])).

tff(c_50,plain,(
    ! [A_21,B_22] : k3_tarski(k2_tarski(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_153,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_50])).

tff(c_54,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_55,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_54])).

tff(c_170,plain,(
    r1_tarski(k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_55])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_232,plain,
    ( k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5')) = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_170,c_20])).

tff(c_235,plain,(
    k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_232])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_267,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k2_tarski('#skF_6','#skF_5'))
      | r2_hidden(D_50,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_4])).

tff(c_271,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_267])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:43:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.89/1.21  
% 1.89/1.21  %Foreground sorts:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Background operators:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Foreground operators:
% 1.89/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.89/1.21  tff('#skF_7', type, '#skF_7': $i).
% 1.89/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.89/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.89/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.21  
% 1.89/1.22  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.89/1.22  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.89/1.22  tff(f_42, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.89/1.22  tff(f_44, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.89/1.22  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.89/1.22  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.89/1.22  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.89/1.22  tff(c_52, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.22  tff(c_32, plain, (![D_18, A_13]: (r2_hidden(D_18, k2_tarski(A_13, D_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.89/1.22  tff(c_26, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.89/1.22  tff(c_28, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.89/1.22  tff(c_110, plain, (![A_32, B_33]: (k3_tarski(k2_tarski(A_32, B_33))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.22  tff(c_147, plain, (![B_38, A_39]: (k3_tarski(k2_tarski(B_38, A_39))=k2_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_28, c_110])).
% 1.89/1.22  tff(c_50, plain, (![A_21, B_22]: (k3_tarski(k2_tarski(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.89/1.22  tff(c_153, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_147, c_50])).
% 1.89/1.22  tff(c_54, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.22  tff(c_55, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_54])).
% 1.89/1.22  tff(c_170, plain, (r1_tarski(k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_55])).
% 1.89/1.22  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.89/1.22  tff(c_232, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5'))='#skF_7' | ~r1_tarski('#skF_7', k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_170, c_20])).
% 1.89/1.22  tff(c_235, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_232])).
% 1.89/1.22  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.89/1.22  tff(c_267, plain, (![D_50]: (~r2_hidden(D_50, k2_tarski('#skF_6', '#skF_5')) | r2_hidden(D_50, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_4])).
% 1.89/1.22  tff(c_271, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_32, c_267])).
% 1.89/1.22  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_271])).
% 1.89/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  Inference rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Ref     : 0
% 1.89/1.22  #Sup     : 54
% 1.89/1.22  #Fact    : 0
% 1.89/1.22  #Define  : 0
% 1.89/1.22  #Split   : 0
% 1.89/1.22  #Chain   : 0
% 1.89/1.22  #Close   : 0
% 1.89/1.22  
% 1.89/1.22  Ordering : KBO
% 1.89/1.22  
% 1.89/1.22  Simplification rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Subsume      : 5
% 1.89/1.22  #Demod        : 22
% 1.89/1.22  #Tautology    : 40
% 1.89/1.22  #SimpNegUnit  : 1
% 1.89/1.22  #BackRed      : 2
% 1.89/1.22  
% 1.89/1.22  #Partial instantiations: 0
% 1.89/1.22  #Strategies tried      : 1
% 1.89/1.22  
% 1.89/1.22  Timing (in seconds)
% 1.89/1.22  ----------------------
% 1.89/1.23  Preprocessing        : 0.30
% 1.89/1.23  Parsing              : 0.15
% 1.89/1.23  CNF conversion       : 0.02
% 1.89/1.23  Main loop            : 0.17
% 1.89/1.23  Inferencing          : 0.05
% 1.89/1.23  Reduction            : 0.07
% 1.89/1.23  Demodulation         : 0.05
% 1.89/1.23  BG Simplification    : 0.01
% 1.89/1.23  Subsumption          : 0.04
% 1.89/1.23  Abstraction          : 0.01
% 1.89/1.23  MUC search           : 0.00
% 1.89/1.23  Cooper               : 0.00
% 1.89/1.23  Total                : 0.50
% 1.89/1.23  Index Insertion      : 0.00
% 1.89/1.23  Index Deletion       : 0.00
% 1.89/1.23  Index Matching       : 0.00
% 1.89/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
