%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:13 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  68 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_26,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_50,plain,(
    ! [D_27,A_28] : r2_hidden(D_27,k2_tarski(A_28,D_27)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_50])).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(k1_tarski(A_24),B_25)
      | r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_40,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_70,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_70])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    ! [C_5] :
      ( ~ r1_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))
      | ~ r2_hidden(C_5,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_4])).

tff(c_120,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_124,plain,(
    r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_120])).

tff(c_8,plain,(
    ! [D_13,B_9,A_8] :
      ( D_13 = B_9
      | D_13 = A_8
      | ~ r2_hidden(D_13,k2_tarski(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_127,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_124,c_8])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_127])).

tff(c_135,plain,(
    ! [C_51] : ~ r2_hidden(C_51,k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_140,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_53,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.57  
% 2.31/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.31/1.57  
% 2.31/1.57  %Foreground sorts:
% 2.31/1.57  
% 2.31/1.57  
% 2.31/1.57  %Background operators:
% 2.31/1.57  
% 2.31/1.57  
% 2.31/1.57  %Foreground operators:
% 2.31/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.57  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.57  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.31/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.31/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.57  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.31/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.31/1.57  
% 2.31/1.59  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.31/1.59  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.31/1.59  tff(f_75, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.31/1.59  tff(f_65, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.31/1.59  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.31/1.59  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.31/1.59  tff(c_26, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.31/1.59  tff(c_50, plain, (![D_27, A_28]: (r2_hidden(D_27, k2_tarski(A_28, D_27)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.31/1.59  tff(c_53, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_50])).
% 2.31/1.59  tff(c_38, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.59  tff(c_36, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.59  tff(c_34, plain, (![A_24, B_25]: (r1_xboole_0(k1_tarski(A_24), B_25) | r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.59  tff(c_40, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.59  tff(c_70, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.31/1.59  tff(c_74, plain, (k3_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_40, c_70])).
% 2.31/1.59  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.59  tff(c_79, plain, (![C_5]: (~r1_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')) | ~r2_hidden(C_5, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_74, c_4])).
% 2.31/1.59  tff(c_120, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_79])).
% 2.31/1.59  tff(c_124, plain, (r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_120])).
% 2.31/1.59  tff(c_8, plain, (![D_13, B_9, A_8]: (D_13=B_9 | D_13=A_8 | ~r2_hidden(D_13, k2_tarski(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.31/1.59  tff(c_127, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_124, c_8])).
% 2.31/1.59  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_127])).
% 2.31/1.59  tff(c_135, plain, (![C_51]: (~r2_hidden(C_51, k1_tarski('#skF_4')))), inference(splitRight, [status(thm)], [c_79])).
% 2.31/1.59  tff(c_140, plain, $false, inference(resolution, [status(thm)], [c_53, c_135])).
% 2.31/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.59  
% 2.31/1.59  Inference rules
% 2.31/1.59  ----------------------
% 2.31/1.59  #Ref     : 0
% 2.31/1.59  #Sup     : 21
% 2.31/1.59  #Fact    : 0
% 2.31/1.59  #Define  : 0
% 2.31/1.59  #Split   : 2
% 2.31/1.59  #Chain   : 0
% 2.31/1.59  #Close   : 0
% 2.31/1.59  
% 2.31/1.59  Ordering : KBO
% 2.31/1.59  
% 2.31/1.59  Simplification rules
% 2.31/1.59  ----------------------
% 2.31/1.59  #Subsume      : 0
% 2.31/1.59  #Demod        : 1
% 2.31/1.59  #Tautology    : 13
% 2.31/1.59  #SimpNegUnit  : 1
% 2.31/1.59  #BackRed      : 0
% 2.31/1.59  
% 2.31/1.59  #Partial instantiations: 0
% 2.31/1.59  #Strategies tried      : 1
% 2.31/1.59  
% 2.31/1.59  Timing (in seconds)
% 2.31/1.59  ----------------------
% 2.31/1.59  Preprocessing        : 0.49
% 2.31/1.60  Parsing              : 0.25
% 2.31/1.60  CNF conversion       : 0.04
% 2.31/1.60  Main loop            : 0.22
% 2.31/1.60  Inferencing          : 0.07
% 2.31/1.60  Reduction            : 0.07
% 2.31/1.60  Demodulation         : 0.05
% 2.31/1.60  BG Simplification    : 0.02
% 2.31/1.60  Subsumption          : 0.05
% 2.31/1.60  Abstraction          : 0.01
% 2.31/1.60  MUC search           : 0.00
% 2.31/1.60  Cooper               : 0.00
% 2.31/1.60  Total                : 0.76
% 2.31/1.60  Index Insertion      : 0.00
% 2.31/1.60  Index Deletion       : 0.00
% 2.31/1.60  Index Matching       : 0.00
% 2.31/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
