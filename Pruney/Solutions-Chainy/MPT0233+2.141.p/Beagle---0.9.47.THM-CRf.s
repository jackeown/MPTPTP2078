%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:39 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  43 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_46,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [D_14,B_10] : r2_hidden(D_14,k2_tarski(D_14,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_60,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_60])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_97,plain,(
    ! [D_40] :
      ( r2_hidden(D_40,k2_tarski('#skF_7','#skF_8'))
      | ~ r2_hidden(D_40,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4])).

tff(c_22,plain,(
    ! [D_14,B_10,A_9] :
      ( D_14 = B_10
      | D_14 = A_9
      | ~ r2_hidden(D_14,k2_tarski(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [D_41] :
      ( D_41 = '#skF_8'
      | D_41 = '#skF_7'
      | ~ r2_hidden(D_41,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_97,c_22])).

tff(c_110,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_26,c_102])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:27:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 1.91/1.18  
% 1.91/1.18  %Foreground sorts:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Background operators:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Foreground operators:
% 1.91/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.91/1.18  tff('#skF_7', type, '#skF_7': $i).
% 1.91/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.91/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.18  tff('#skF_8', type, '#skF_8': $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.18  
% 1.91/1.19  tff(f_61, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.91/1.19  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.91/1.19  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.91/1.19  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.91/1.19  tff(c_46, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.19  tff(c_44, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.19  tff(c_26, plain, (![D_14, B_10]: (r2_hidden(D_14, k2_tarski(D_14, B_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.19  tff(c_48, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.19  tff(c_60, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.19  tff(c_64, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_60])).
% 1.91/1.19  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.19  tff(c_97, plain, (![D_40]: (r2_hidden(D_40, k2_tarski('#skF_7', '#skF_8')) | ~r2_hidden(D_40, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_4])).
% 1.91/1.19  tff(c_22, plain, (![D_14, B_10, A_9]: (D_14=B_10 | D_14=A_9 | ~r2_hidden(D_14, k2_tarski(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.19  tff(c_102, plain, (![D_41]: (D_41='#skF_8' | D_41='#skF_7' | ~r2_hidden(D_41, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_97, c_22])).
% 1.91/1.19  tff(c_110, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_26, c_102])).
% 1.91/1.19  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_110])).
% 1.91/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  Inference rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Ref     : 0
% 1.91/1.19  #Sup     : 14
% 1.91/1.19  #Fact    : 0
% 1.91/1.19  #Define  : 0
% 1.91/1.19  #Split   : 0
% 1.91/1.19  #Chain   : 0
% 1.91/1.19  #Close   : 0
% 1.91/1.19  
% 1.91/1.19  Ordering : KBO
% 1.91/1.19  
% 1.91/1.19  Simplification rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Subsume      : 0
% 1.91/1.19  #Demod        : 0
% 1.91/1.19  #Tautology    : 9
% 1.91/1.19  #SimpNegUnit  : 1
% 1.91/1.19  #BackRed      : 0
% 1.91/1.19  
% 1.91/1.19  #Partial instantiations: 0
% 1.91/1.19  #Strategies tried      : 1
% 1.91/1.19  
% 1.91/1.19  Timing (in seconds)
% 1.91/1.19  ----------------------
% 1.91/1.20  Preprocessing        : 0.32
% 1.91/1.20  Parsing              : 0.16
% 1.91/1.20  CNF conversion       : 0.02
% 1.91/1.20  Main loop            : 0.13
% 1.91/1.20  Inferencing          : 0.04
% 1.91/1.20  Reduction            : 0.04
% 1.91/1.20  Demodulation         : 0.03
% 1.91/1.20  BG Simplification    : 0.02
% 1.91/1.20  Subsumption          : 0.03
% 1.91/1.20  Abstraction          : 0.01
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.47
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.20  Index Deletion       : 0.00
% 1.91/1.20  Index Matching       : 0.00
% 1.91/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
