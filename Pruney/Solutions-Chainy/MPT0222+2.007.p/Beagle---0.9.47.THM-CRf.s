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
% DateTime   : Thu Dec  3 09:48:16 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  28 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_28,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(k1_tarski(A_18),B_19)
      | r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_26])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,(
    ! [D_22,B_23,A_24] :
      ( D_22 = B_23
      | D_22 = A_24
      | ~ r2_hidden(D_22,k2_tarski(A_24,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [D_25,A_26] :
      ( D_25 = A_26
      | D_25 = A_26
      | ~ r2_hidden(D_25,k1_tarski(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_79,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_76])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.20  
% 1.62/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.21  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.62/1.21  
% 1.62/1.21  %Foreground sorts:
% 1.62/1.21  
% 1.62/1.21  
% 1.62/1.21  %Background operators:
% 1.62/1.21  
% 1.62/1.21  
% 1.62/1.21  %Foreground operators:
% 1.62/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.62/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.62/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.62/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.62/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.62/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.21  
% 1.62/1.22  tff(f_49, negated_conjecture, ~(![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.62/1.22  tff(f_43, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.62/1.22  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.62/1.22  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.62/1.22  tff(c_28, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.62/1.22  tff(c_48, plain, (![A_18, B_19]: (r1_xboole_0(k1_tarski(A_18), B_19) | r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.62/1.22  tff(c_26, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.62/1.22  tff(c_52, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_26])).
% 1.62/1.22  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.22  tff(c_62, plain, (![D_22, B_23, A_24]: (D_22=B_23 | D_22=A_24 | ~r2_hidden(D_22, k2_tarski(A_24, B_23)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.62/1.22  tff(c_76, plain, (![D_25, A_26]: (D_25=A_26 | D_25=A_26 | ~r2_hidden(D_25, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_62])).
% 1.62/1.22  tff(c_79, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_52, c_76])).
% 1.62/1.22  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_79])).
% 1.62/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.22  
% 1.62/1.22  Inference rules
% 1.62/1.22  ----------------------
% 1.62/1.22  #Ref     : 0
% 1.62/1.22  #Sup     : 12
% 1.62/1.22  #Fact    : 0
% 1.62/1.22  #Define  : 0
% 1.62/1.22  #Split   : 0
% 1.62/1.22  #Chain   : 0
% 1.62/1.22  #Close   : 0
% 1.62/1.22  
% 1.62/1.22  Ordering : KBO
% 1.62/1.22  
% 1.62/1.22  Simplification rules
% 1.62/1.22  ----------------------
% 1.62/1.22  #Subsume      : 0
% 1.62/1.22  #Demod        : 1
% 1.62/1.22  #Tautology    : 7
% 1.62/1.22  #SimpNegUnit  : 1
% 1.62/1.22  #BackRed      : 0
% 1.62/1.22  
% 1.62/1.22  #Partial instantiations: 0
% 1.62/1.22  #Strategies tried      : 1
% 1.62/1.22  
% 1.62/1.22  Timing (in seconds)
% 1.62/1.22  ----------------------
% 1.62/1.23  Preprocessing        : 0.25
% 1.62/1.23  Parsing              : 0.12
% 1.62/1.23  CNF conversion       : 0.02
% 1.62/1.23  Main loop            : 0.11
% 1.62/1.23  Inferencing          : 0.04
% 1.62/1.23  Reduction            : 0.03
% 1.62/1.23  Demodulation         : 0.02
% 1.62/1.23  BG Simplification    : 0.01
% 1.62/1.23  Subsumption          : 0.02
% 1.62/1.23  Abstraction          : 0.01
% 1.62/1.23  MUC search           : 0.00
% 1.62/1.23  Cooper               : 0.00
% 1.62/1.23  Total                : 0.39
% 1.62/1.23  Index Insertion      : 0.00
% 1.62/1.23  Index Deletion       : 0.00
% 1.62/1.23  Index Matching       : 0.00
% 1.62/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
