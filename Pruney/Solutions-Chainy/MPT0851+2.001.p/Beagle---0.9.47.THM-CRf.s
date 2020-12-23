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
% DateTime   : Thu Dec  3 10:08:50 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    3
%              Number of atoms          :   22 (  26 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k1_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ! [B] :
          ( B = k2_mcart_1(A)
        <=> ! [C,D] :
              ( A = k4_tarski(C,D)
             => B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_mcart_1(k4_tarski(A,B)) = A
        & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_2,plain,(
    ! [C_20,D_21,B_13,C_14] :
      ( k1_mcart_1(k4_tarski(C_20,D_21)) = C_20
      | k4_tarski(C_20,D_21) != k4_tarski(B_13,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40,plain,(
    ! [B_13,C_14] : k1_mcart_1(k4_tarski(B_13,C_14)) = B_13 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_8,plain,(
    ! [C_41,D_42,B_34,C_35] :
      ( k2_mcart_1(k4_tarski(C_41,D_42)) = D_42
      | k4_tarski(C_41,D_42) != k4_tarski(B_34,C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [B_34,C_35] : k2_mcart_1(k4_tarski(B_34,C_35)) = C_35 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8])).

tff(c_14,plain,
    ( k1_mcart_1(k4_tarski('#skF_7','#skF_8')) != '#skF_7'
    | k2_mcart_1(k4_tarski('#skF_5','#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_15,plain,(
    k2_mcart_1(k4_tarski('#skF_5','#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_30,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_15])).

tff(c_31,plain,(
    k1_mcart_1(k4_tarski('#skF_7','#skF_8')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:21:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  %$ k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 1.70/1.16  
% 1.70/1.16  %Foreground sorts:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Background operators:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Foreground operators:
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.70/1.16  tff('#skF_7', type, '#skF_7': $i).
% 1.70/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.70/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.70/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.70/1.16  tff('#skF_8', type, '#skF_8': $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.70/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.70/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.70/1.16  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.70/1.16  
% 1.70/1.17  tff(f_36, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (![B]: ((B = k1_mcart_1(A)) <=> (![C, D]: ((A = k4_tarski(C, D)) => (B = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_mcart_1)).
% 1.70/1.17  tff(f_47, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (![B]: ((B = k2_mcart_1(A)) <=> (![C, D]: ((A = k4_tarski(C, D)) => (B = D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_mcart_1)).
% 1.70/1.17  tff(f_52, negated_conjecture, ~(![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.70/1.17  tff(c_2, plain, (![C_20, D_21, B_13, C_14]: (k1_mcart_1(k4_tarski(C_20, D_21))=C_20 | k4_tarski(C_20, D_21)!=k4_tarski(B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.70/1.17  tff(c_40, plain, (![B_13, C_14]: (k1_mcart_1(k4_tarski(B_13, C_14))=B_13)), inference(reflexivity, [status(thm), theory('equality')], [c_2])).
% 1.70/1.17  tff(c_8, plain, (![C_41, D_42, B_34, C_35]: (k2_mcart_1(k4_tarski(C_41, D_42))=D_42 | k4_tarski(C_41, D_42)!=k4_tarski(B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.70/1.17  tff(c_20, plain, (![B_34, C_35]: (k2_mcart_1(k4_tarski(B_34, C_35))=C_35)), inference(reflexivity, [status(thm), theory('equality')], [c_8])).
% 1.70/1.17  tff(c_14, plain, (k1_mcart_1(k4_tarski('#skF_7', '#skF_8'))!='#skF_7' | k2_mcart_1(k4_tarski('#skF_5', '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.70/1.17  tff(c_15, plain, (k2_mcart_1(k4_tarski('#skF_5', '#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_14])).
% 1.70/1.17  tff(c_30, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_15])).
% 1.70/1.17  tff(c_31, plain, (k1_mcart_1(k4_tarski('#skF_7', '#skF_8'))!='#skF_7'), inference(splitRight, [status(thm)], [c_14])).
% 1.70/1.17  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_31])).
% 1.70/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  Inference rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Ref     : 3
% 1.70/1.17  #Sup     : 2
% 1.70/1.17  #Fact    : 0
% 1.70/1.17  #Define  : 0
% 1.70/1.17  #Split   : 1
% 1.70/1.17  #Chain   : 0
% 1.70/1.17  #Close   : 0
% 1.70/1.17  
% 1.70/1.17  Ordering : KBO
% 1.70/1.17  
% 1.70/1.17  Simplification rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Subsume      : 0
% 1.70/1.17  #Demod        : 5
% 1.70/1.17  #Tautology    : 4
% 1.70/1.17  #SimpNegUnit  : 0
% 1.70/1.17  #BackRed      : 3
% 1.70/1.17  
% 1.70/1.17  #Partial instantiations: 0
% 1.70/1.17  #Strategies tried      : 1
% 1.70/1.17  
% 1.70/1.17  Timing (in seconds)
% 1.70/1.17  ----------------------
% 1.70/1.17  Preprocessing        : 0.27
% 1.70/1.17  Parsing              : 0.14
% 1.70/1.17  CNF conversion       : 0.02
% 1.70/1.17  Main loop            : 0.08
% 1.70/1.17  Inferencing          : 0.03
% 1.70/1.17  Reduction            : 0.02
% 1.70/1.17  Demodulation         : 0.01
% 1.70/1.17  BG Simplification    : 0.01
% 1.70/1.17  Subsumption          : 0.01
% 1.70/1.17  Abstraction          : 0.00
% 1.70/1.17  MUC search           : 0.00
% 1.70/1.17  Cooper               : 0.00
% 1.70/1.17  Total                : 0.36
% 1.70/1.18  Index Insertion      : 0.00
% 1.70/1.18  Index Deletion       : 0.00
% 1.70/1.18  Index Matching       : 0.00
% 1.70/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
