%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:03 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  41 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_42,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_119,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_121,plain,
    ( k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_46,c_119])).

tff(c_130,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_121])).

tff(c_51,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_33,B_32] : r1_tarski(A_33,k2_xboole_0(B_32,A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_18])).

tff(c_142,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_66])).

tff(c_24,plain,(
    ! [D_20,B_16] : r2_hidden(D_20,k2_tarski(D_20,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_193,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_295,plain,(
    ! [D_69,B_70,B_71] :
      ( r2_hidden(D_69,B_70)
      | ~ r1_tarski(k2_tarski(D_69,B_71),B_70) ) ),
    inference(resolution,[status(thm)],[c_24,c_193])).

tff(c_306,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_142,c_295])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.29  
% 1.97/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.30  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.97/1.30  
% 1.97/1.30  %Foreground sorts:
% 1.97/1.30  
% 1.97/1.30  
% 1.97/1.30  %Background operators:
% 1.97/1.30  
% 1.97/1.30  
% 1.97/1.30  %Foreground operators:
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.30  tff('#skF_6', type, '#skF_6': $i).
% 1.97/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.97/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.30  
% 2.21/1.31  tff(f_64, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.21/1.31  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.21/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.21/1.31  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.21/1.31  tff(f_55, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.21/1.31  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.21/1.31  tff(c_42, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.21/1.31  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.31  tff(c_44, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.21/1.31  tff(c_46, plain, (r1_tarski(k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 2.21/1.31  tff(c_119, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.21/1.31  tff(c_121, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_46, c_119])).
% 2.21/1.31  tff(c_130, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_121])).
% 2.21/1.31  tff(c_51, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.31  tff(c_66, plain, (![A_33, B_32]: (r1_tarski(A_33, k2_xboole_0(B_32, A_33)))), inference(superposition, [status(thm), theory('equality')], [c_51, c_18])).
% 2.21/1.31  tff(c_142, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_130, c_66])).
% 2.21/1.31  tff(c_24, plain, (![D_20, B_16]: (r2_hidden(D_20, k2_tarski(D_20, B_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.21/1.31  tff(c_193, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.21/1.31  tff(c_295, plain, (![D_69, B_70, B_71]: (r2_hidden(D_69, B_70) | ~r1_tarski(k2_tarski(D_69, B_71), B_70))), inference(resolution, [status(thm)], [c_24, c_193])).
% 2.21/1.31  tff(c_306, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_142, c_295])).
% 2.21/1.31  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_306])).
% 2.21/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.31  
% 2.21/1.31  Inference rules
% 2.21/1.31  ----------------------
% 2.21/1.31  #Ref     : 0
% 2.21/1.31  #Sup     : 63
% 2.21/1.31  #Fact    : 0
% 2.21/1.31  #Define  : 0
% 2.21/1.31  #Split   : 1
% 2.21/1.31  #Chain   : 0
% 2.21/1.31  #Close   : 0
% 2.21/1.31  
% 2.21/1.31  Ordering : KBO
% 2.21/1.31  
% 2.21/1.31  Simplification rules
% 2.21/1.31  ----------------------
% 2.21/1.31  #Subsume      : 3
% 2.21/1.31  #Demod        : 18
% 2.21/1.31  #Tautology    : 32
% 2.21/1.31  #SimpNegUnit  : 1
% 2.21/1.31  #BackRed      : 1
% 2.21/1.31  
% 2.21/1.31  #Partial instantiations: 0
% 2.21/1.31  #Strategies tried      : 1
% 2.21/1.31  
% 2.21/1.31  Timing (in seconds)
% 2.21/1.31  ----------------------
% 2.21/1.31  Preprocessing        : 0.31
% 2.21/1.31  Parsing              : 0.17
% 2.21/1.31  CNF conversion       : 0.02
% 2.21/1.31  Main loop            : 0.21
% 2.21/1.31  Inferencing          : 0.07
% 2.21/1.31  Reduction            : 0.07
% 2.21/1.31  Demodulation         : 0.05
% 2.21/1.31  BG Simplification    : 0.01
% 2.21/1.31  Subsumption          : 0.04
% 2.21/1.31  Abstraction          : 0.01
% 2.21/1.31  MUC search           : 0.00
% 2.21/1.31  Cooper               : 0.00
% 2.21/1.31  Total                : 0.54
% 2.21/1.31  Index Insertion      : 0.00
% 2.21/1.31  Index Deletion       : 0.00
% 2.21/1.31  Index Matching       : 0.00
% 2.21/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
