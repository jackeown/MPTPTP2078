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
% DateTime   : Thu Dec  3 09:50:36 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  38 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_54,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,(
    ! [D_26,A_27] : r2_hidden(D_26,k2_tarski(A_27,D_26)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    ! [A_19] : r2_hidden(A_19,k1_tarski(A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_69])).

tff(c_28,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k1_tarski('#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_177,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_181,plain,
    ( k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_58,c_177])).

tff(c_191,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_181])).

tff(c_228,plain,(
    ! [D_48,B_49,A_50] :
      ( ~ r2_hidden(D_48,B_49)
      | r2_hidden(D_48,k2_xboole_0(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_241,plain,(
    ! [D_51] :
      ( ~ r2_hidden(D_51,k1_tarski('#skF_5'))
      | r2_hidden(D_51,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_228])).

tff(c_245,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_241])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.28  
% 1.97/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.28  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.97/1.28  
% 1.97/1.28  %Foreground sorts:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Background operators:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Foreground operators:
% 1.97/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.97/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.28  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.28  tff('#skF_6', type, '#skF_6': $i).
% 1.97/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.97/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.28  
% 1.97/1.29  tff(f_64, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.97/1.29  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.97/1.29  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.97/1.29  tff(f_44, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.97/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.97/1.29  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.97/1.29  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.97/1.29  tff(c_54, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.29  tff(c_48, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.29  tff(c_69, plain, (![D_26, A_27]: (r2_hidden(D_26, k2_tarski(A_27, D_26)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.97/1.29  tff(c_72, plain, (![A_19]: (r2_hidden(A_19, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_69])).
% 1.97/1.29  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.97/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.29  tff(c_56, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.29  tff(c_58, plain, (r1_tarski(k2_xboole_0('#skF_6', k1_tarski('#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_56])).
% 1.97/1.29  tff(c_177, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.97/1.29  tff(c_181, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_58, c_177])).
% 1.97/1.29  tff(c_191, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_181])).
% 1.97/1.29  tff(c_228, plain, (![D_48, B_49, A_50]: (~r2_hidden(D_48, B_49) | r2_hidden(D_48, k2_xboole_0(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.97/1.29  tff(c_241, plain, (![D_51]: (~r2_hidden(D_51, k1_tarski('#skF_5')) | r2_hidden(D_51, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_228])).
% 1.97/1.29  tff(c_245, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_72, c_241])).
% 1.97/1.29  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_245])).
% 1.97/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.29  
% 1.97/1.29  Inference rules
% 1.97/1.29  ----------------------
% 1.97/1.29  #Ref     : 0
% 1.97/1.29  #Sup     : 47
% 1.97/1.29  #Fact    : 0
% 1.97/1.29  #Define  : 0
% 1.97/1.29  #Split   : 1
% 1.97/1.29  #Chain   : 0
% 1.97/1.29  #Close   : 0
% 1.97/1.29  
% 1.97/1.29  Ordering : KBO
% 1.97/1.29  
% 1.97/1.29  Simplification rules
% 1.97/1.29  ----------------------
% 1.97/1.29  #Subsume      : 4
% 1.97/1.29  #Demod        : 13
% 1.97/1.29  #Tautology    : 29
% 1.97/1.29  #SimpNegUnit  : 1
% 1.97/1.29  #BackRed      : 1
% 1.97/1.29  
% 1.97/1.29  #Partial instantiations: 0
% 1.97/1.29  #Strategies tried      : 1
% 1.97/1.29  
% 1.97/1.29  Timing (in seconds)
% 1.97/1.29  ----------------------
% 1.97/1.30  Preprocessing        : 0.32
% 1.97/1.30  Parsing              : 0.16
% 1.97/1.30  CNF conversion       : 0.02
% 1.97/1.30  Main loop            : 0.17
% 1.97/1.30  Inferencing          : 0.05
% 1.97/1.30  Reduction            : 0.06
% 1.97/1.30  Demodulation         : 0.05
% 1.97/1.30  BG Simplification    : 0.01
% 1.97/1.30  Subsumption          : 0.04
% 1.97/1.30  Abstraction          : 0.01
% 1.97/1.30  MUC search           : 0.00
% 1.97/1.30  Cooper               : 0.00
% 1.97/1.30  Total                : 0.52
% 1.97/1.30  Index Insertion      : 0.00
% 1.97/1.30  Index Deletion       : 0.00
% 1.97/1.30  Index Matching       : 0.00
% 1.97/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
