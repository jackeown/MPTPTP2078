%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:12 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  39 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_32,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [D_16,B_17] : r2_hidden(D_16,k2_tarski(D_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_44])).

tff(c_101,plain,(
    ! [C_33,B_34,A_35] :
      ( r2_hidden(C_33,B_34)
      | ~ r2_hidden(C_33,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,(
    ! [A_36,B_37] :
      ( r2_hidden(A_36,B_37)
      | ~ r1_tarski(k1_tarski(A_36),B_37) ) ),
    inference(resolution,[status(thm)],[c_47,c_101])).

tff(c_124,plain,(
    r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_114])).

tff(c_8,plain,(
    ! [D_11,B_7,A_6] :
      ( D_11 = B_7
      | D_11 = A_6
      | ~ r2_hidden(D_11,k2_tarski(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_124,c_8])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.30  
% 1.97/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.30  %$ r2_hidden > r1_tarski > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
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
% 1.97/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.30  tff('#skF_6', type, '#skF_6': $i).
% 1.97/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.97/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.30  
% 1.97/1.31  tff(f_55, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.97/1.31  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.97/1.31  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.97/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.97/1.31  tff(c_32, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.31  tff(c_30, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.31  tff(c_34, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.31  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.31  tff(c_44, plain, (![D_16, B_17]: (r2_hidden(D_16, k2_tarski(D_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.31  tff(c_47, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_44])).
% 1.97/1.31  tff(c_101, plain, (![C_33, B_34, A_35]: (r2_hidden(C_33, B_34) | ~r2_hidden(C_33, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.31  tff(c_114, plain, (![A_36, B_37]: (r2_hidden(A_36, B_37) | ~r1_tarski(k1_tarski(A_36), B_37))), inference(resolution, [status(thm)], [c_47, c_101])).
% 1.97/1.31  tff(c_124, plain, (r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_114])).
% 1.97/1.31  tff(c_8, plain, (![D_11, B_7, A_6]: (D_11=B_7 | D_11=A_6 | ~r2_hidden(D_11, k2_tarski(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.31  tff(c_130, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_124, c_8])).
% 1.97/1.31  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_130])).
% 1.97/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.31  
% 1.97/1.31  Inference rules
% 1.97/1.31  ----------------------
% 1.97/1.31  #Ref     : 0
% 1.97/1.31  #Sup     : 21
% 1.97/1.31  #Fact    : 0
% 1.97/1.31  #Define  : 0
% 1.97/1.31  #Split   : 0
% 1.97/1.31  #Chain   : 0
% 1.97/1.31  #Close   : 0
% 1.97/1.31  
% 1.97/1.31  Ordering : KBO
% 1.97/1.31  
% 1.97/1.31  Simplification rules
% 1.97/1.31  ----------------------
% 1.97/1.31  #Subsume      : 0
% 1.97/1.31  #Demod        : 2
% 1.97/1.31  #Tautology    : 9
% 1.97/1.31  #SimpNegUnit  : 1
% 1.97/1.31  #BackRed      : 0
% 1.97/1.31  
% 1.97/1.31  #Partial instantiations: 0
% 1.97/1.31  #Strategies tried      : 1
% 1.97/1.31  
% 1.97/1.31  Timing (in seconds)
% 1.97/1.31  ----------------------
% 1.97/1.32  Preprocessing        : 0.34
% 1.97/1.32  Parsing              : 0.16
% 1.97/1.32  CNF conversion       : 0.03
% 1.97/1.32  Main loop            : 0.12
% 1.97/1.32  Inferencing          : 0.04
% 1.97/1.32  Reduction            : 0.04
% 1.97/1.32  Demodulation         : 0.03
% 1.97/1.32  BG Simplification    : 0.02
% 1.97/1.32  Subsumption          : 0.02
% 1.97/1.32  Abstraction          : 0.01
% 1.97/1.32  MUC search           : 0.00
% 1.97/1.32  Cooper               : 0.00
% 1.97/1.32  Total                : 0.48
% 1.97/1.32  Index Insertion      : 0.00
% 1.97/1.32  Index Deletion       : 0.00
% 1.97/1.32  Index Matching       : 0.00
% 1.97/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
