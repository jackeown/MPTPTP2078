%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:59 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  39 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  39 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
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

tff(c_54,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_52,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_56,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_68,plain,(
    ! [A_57] : k2_tarski(A_57,A_57) = k1_tarski(A_57) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [D_19,A_14] : r2_hidden(D_19,k2_tarski(A_14,D_19)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_74,plain,(
    ! [A_57] : r2_hidden(A_57,k1_tarski(A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_18])).

tff(c_262,plain,(
    ! [C_79,B_80,A_81] :
      ( r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_275,plain,(
    ! [A_82,B_83] :
      ( r2_hidden(A_82,B_83)
      | ~ r1_tarski(k1_tarski(A_82),B_83) ) ),
    inference(resolution,[status(thm)],[c_74,c_262])).

tff(c_285,plain,(
    r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_275])).

tff(c_16,plain,(
    ! [D_19,B_15,A_14] :
      ( D_19 = B_15
      | D_19 = A_14
      | ~ r2_hidden(D_19,k2_tarski(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_290,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_285,c_16])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.19/1.30  
% 2.19/1.30  %Foreground sorts:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Background operators:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Foreground operators:
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.30  
% 2.19/1.31  tff(f_79, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.19/1.31  tff(f_63, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.19/1.31  tff(f_51, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.19/1.31  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.19/1.31  tff(c_54, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.19/1.31  tff(c_52, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.19/1.31  tff(c_56, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.19/1.31  tff(c_68, plain, (![A_57]: (k2_tarski(A_57, A_57)=k1_tarski(A_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.19/1.31  tff(c_18, plain, (![D_19, A_14]: (r2_hidden(D_19, k2_tarski(A_14, D_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.31  tff(c_74, plain, (![A_57]: (r2_hidden(A_57, k1_tarski(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_18])).
% 2.19/1.31  tff(c_262, plain, (![C_79, B_80, A_81]: (r2_hidden(C_79, B_80) | ~r2_hidden(C_79, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.31  tff(c_275, plain, (![A_82, B_83]: (r2_hidden(A_82, B_83) | ~r1_tarski(k1_tarski(A_82), B_83))), inference(resolution, [status(thm)], [c_74, c_262])).
% 2.19/1.31  tff(c_285, plain, (r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_275])).
% 2.19/1.31  tff(c_16, plain, (![D_19, B_15, A_14]: (D_19=B_15 | D_19=A_14 | ~r2_hidden(D_19, k2_tarski(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.19/1.31  tff(c_290, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_285, c_16])).
% 2.19/1.31  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_290])).
% 2.19/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.31  
% 2.19/1.31  Inference rules
% 2.19/1.31  ----------------------
% 2.19/1.31  #Ref     : 0
% 2.19/1.31  #Sup     : 55
% 2.19/1.31  #Fact    : 0
% 2.19/1.31  #Define  : 0
% 2.19/1.31  #Split   : 0
% 2.19/1.31  #Chain   : 0
% 2.19/1.31  #Close   : 0
% 2.19/1.31  
% 2.19/1.31  Ordering : KBO
% 2.19/1.31  
% 2.19/1.31  Simplification rules
% 2.19/1.31  ----------------------
% 2.19/1.31  #Subsume      : 0
% 2.19/1.31  #Demod        : 32
% 2.19/1.31  #Tautology    : 39
% 2.19/1.31  #SimpNegUnit  : 1
% 2.19/1.31  #BackRed      : 0
% 2.19/1.31  
% 2.19/1.31  #Partial instantiations: 0
% 2.19/1.31  #Strategies tried      : 1
% 2.19/1.31  
% 2.19/1.31  Timing (in seconds)
% 2.19/1.31  ----------------------
% 2.19/1.32  Preprocessing        : 0.32
% 2.19/1.32  Parsing              : 0.16
% 2.19/1.32  CNF conversion       : 0.02
% 2.19/1.32  Main loop            : 0.18
% 2.19/1.32  Inferencing          : 0.06
% 2.19/1.32  Reduction            : 0.07
% 2.19/1.32  Demodulation         : 0.06
% 2.19/1.32  BG Simplification    : 0.02
% 2.19/1.32  Subsumption          : 0.03
% 2.19/1.32  Abstraction          : 0.01
% 2.19/1.32  MUC search           : 0.00
% 2.19/1.32  Cooper               : 0.00
% 2.19/1.32  Total                : 0.52
% 2.19/1.32  Index Insertion      : 0.00
% 2.19/1.32  Index Deletion       : 0.00
% 2.19/1.32  Index Matching       : 0.00
% 2.19/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
