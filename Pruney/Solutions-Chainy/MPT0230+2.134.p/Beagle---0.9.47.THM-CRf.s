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
% DateTime   : Thu Dec  3 09:49:13 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  46 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_50,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ! [D_26,B_27] : r2_hidden(D_26,k2_tarski(D_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_62])).

tff(c_52,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_81,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_81])).

tff(c_94,plain,(
    ! [D_38,B_39,A_40] :
      ( r2_hidden(D_38,B_39)
      | ~ r2_hidden(D_38,k3_xboole_0(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_136,plain,(
    ! [D_53] :
      ( r2_hidden(D_53,k2_tarski('#skF_6','#skF_7'))
      | ~ r2_hidden(D_53,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_94])).

tff(c_22,plain,(
    ! [D_14,B_10,A_9] :
      ( D_14 = B_10
      | D_14 = A_9
      | ~ r2_hidden(D_14,k2_tarski(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_141,plain,(
    ! [D_54] :
      ( D_54 = '#skF_7'
      | D_54 = '#skF_6'
      | ~ r2_hidden(D_54,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_136,c_22])).

tff(c_145,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_65,c_141])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:56:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.18  
% 1.69/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.95/1.18  
% 1.95/1.18  %Foreground sorts:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Background operators:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Foreground operators:
% 1.95/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.95/1.18  tff('#skF_7', type, '#skF_7': $i).
% 1.95/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.18  
% 1.95/1.19  tff(f_65, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.95/1.19  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.95/1.19  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.95/1.19  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.95/1.19  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.95/1.19  tff(c_50, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.95/1.19  tff(c_48, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.95/1.19  tff(c_40, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.95/1.19  tff(c_62, plain, (![D_26, B_27]: (r2_hidden(D_26, k2_tarski(D_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.19  tff(c_65, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_62])).
% 1.95/1.19  tff(c_52, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.95/1.19  tff(c_81, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.95/1.19  tff(c_85, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_52, c_81])).
% 1.95/1.19  tff(c_94, plain, (![D_38, B_39, A_40]: (r2_hidden(D_38, B_39) | ~r2_hidden(D_38, k3_xboole_0(A_40, B_39)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.95/1.19  tff(c_136, plain, (![D_53]: (r2_hidden(D_53, k2_tarski('#skF_6', '#skF_7')) | ~r2_hidden(D_53, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_85, c_94])).
% 1.95/1.19  tff(c_22, plain, (![D_14, B_10, A_9]: (D_14=B_10 | D_14=A_9 | ~r2_hidden(D_14, k2_tarski(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.19  tff(c_141, plain, (![D_54]: (D_54='#skF_7' | D_54='#skF_6' | ~r2_hidden(D_54, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_136, c_22])).
% 1.95/1.19  tff(c_145, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_65, c_141])).
% 1.95/1.19  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_145])).
% 1.95/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  Inference rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Ref     : 0
% 1.95/1.19  #Sup     : 21
% 1.95/1.19  #Fact    : 0
% 1.95/1.19  #Define  : 0
% 1.95/1.19  #Split   : 0
% 1.95/1.19  #Chain   : 0
% 1.95/1.19  #Close   : 0
% 1.95/1.19  
% 1.95/1.19  Ordering : KBO
% 1.95/1.19  
% 1.95/1.19  Simplification rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Subsume      : 0
% 1.95/1.19  #Demod        : 1
% 1.95/1.19  #Tautology    : 15
% 1.95/1.19  #SimpNegUnit  : 1
% 1.95/1.19  #BackRed      : 0
% 1.95/1.19  
% 1.95/1.19  #Partial instantiations: 0
% 1.95/1.19  #Strategies tried      : 1
% 1.95/1.19  
% 1.95/1.19  Timing (in seconds)
% 1.95/1.19  ----------------------
% 1.95/1.19  Preprocessing        : 0.31
% 1.95/1.19  Parsing              : 0.15
% 1.95/1.19  CNF conversion       : 0.02
% 1.95/1.19  Main loop            : 0.13
% 1.95/1.19  Inferencing          : 0.04
% 1.95/1.19  Reduction            : 0.04
% 1.95/1.19  Demodulation         : 0.03
% 1.95/1.19  BG Simplification    : 0.02
% 1.95/1.19  Subsumption          : 0.03
% 1.95/1.19  Abstraction          : 0.01
% 1.95/1.19  MUC search           : 0.00
% 1.95/1.19  Cooper               : 0.00
% 1.95/1.19  Total                : 0.46
% 1.95/1.19  Index Insertion      : 0.00
% 1.95/1.19  Index Deletion       : 0.00
% 1.95/1.19  Index Matching       : 0.00
% 1.95/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
