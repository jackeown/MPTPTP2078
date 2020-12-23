%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:07 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  38 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_38,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k2_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_34,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_17),B_18),B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_138,plain,
    ( r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5'))
    | ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_34])).

tff(c_142,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_138])).

tff(c_10,plain,(
    ! [D_10,B_6,A_5] :
      ( D_10 = B_6
      | D_10 = A_5
      | ~ r2_hidden(D_10,k2_tarski(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_146,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_142,c_10])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:43:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.25  
% 1.92/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.25  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.92/1.25  
% 1.92/1.25  %Foreground sorts:
% 1.92/1.25  
% 1.92/1.25  
% 1.92/1.25  %Background operators:
% 1.92/1.25  
% 1.92/1.25  
% 1.92/1.25  %Foreground operators:
% 1.92/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.92/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.25  
% 1.92/1.26  tff(f_64, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.92/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.92/1.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.92/1.26  tff(f_54, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 1.92/1.26  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.92/1.26  tff(c_38, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.26  tff(c_36, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.26  tff(c_40, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.26  tff(c_62, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.26  tff(c_69, plain, (k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k2_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_62])).
% 1.92/1.26  tff(c_34, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | ~r1_tarski(k2_xboole_0(k1_tarski(A_17), B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.26  tff(c_138, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5')) | ~r1_tarski(k2_tarski('#skF_4', '#skF_5'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_34])).
% 1.92/1.26  tff(c_142, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_138])).
% 1.92/1.26  tff(c_10, plain, (![D_10, B_6, A_5]: (D_10=B_6 | D_10=A_5 | ~r2_hidden(D_10, k2_tarski(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.92/1.26  tff(c_146, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_142, c_10])).
% 1.92/1.26  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_146])).
% 1.92/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.26  
% 1.92/1.26  Inference rules
% 1.92/1.26  ----------------------
% 1.92/1.26  #Ref     : 0
% 1.92/1.26  #Sup     : 23
% 1.92/1.26  #Fact    : 0
% 1.92/1.26  #Define  : 0
% 1.92/1.26  #Split   : 0
% 1.92/1.26  #Chain   : 0
% 1.92/1.26  #Close   : 0
% 1.92/1.26  
% 1.92/1.26  Ordering : KBO
% 1.92/1.26  
% 1.92/1.26  Simplification rules
% 1.92/1.26  ----------------------
% 1.92/1.26  #Subsume      : 0
% 1.92/1.26  #Demod        : 6
% 1.92/1.26  #Tautology    : 17
% 1.92/1.26  #SimpNegUnit  : 1
% 1.92/1.26  #BackRed      : 0
% 1.92/1.26  
% 1.92/1.26  #Partial instantiations: 0
% 1.92/1.26  #Strategies tried      : 1
% 1.92/1.26  
% 1.92/1.26  Timing (in seconds)
% 1.92/1.26  ----------------------
% 1.92/1.26  Preprocessing        : 0.33
% 1.92/1.26  Parsing              : 0.17
% 1.92/1.26  CNF conversion       : 0.02
% 1.92/1.26  Main loop            : 0.12
% 1.92/1.26  Inferencing          : 0.04
% 1.92/1.26  Reduction            : 0.04
% 1.92/1.26  Demodulation         : 0.03
% 1.92/1.26  BG Simplification    : 0.01
% 1.92/1.26  Subsumption          : 0.02
% 1.92/1.26  Abstraction          : 0.01
% 1.92/1.26  MUC search           : 0.00
% 1.92/1.26  Cooper               : 0.00
% 1.92/1.26  Total                : 0.48
% 1.92/1.26  Index Insertion      : 0.00
% 1.92/1.26  Index Deletion       : 0.00
% 1.92/1.27  Index Matching       : 0.00
% 1.92/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
