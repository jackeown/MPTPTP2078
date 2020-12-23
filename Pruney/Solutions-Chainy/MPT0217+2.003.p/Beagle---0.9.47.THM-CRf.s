%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:45 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   37 (  62 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   35 (  97 expanded)
%              Number of equality atoms :   25 (  76 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( k2_tarski(A,B) = k2_tarski(C,D)
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_zfmisc_1)).

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
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_34,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    r2_hidden('#skF_8',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_16])).

tff(c_75,plain,(
    ! [D_21,B_22,A_23] :
      ( D_21 = B_22
      | D_21 = A_23
      | ~ r2_hidden(D_21,k2_tarski(A_23,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_68,c_75])).

tff(c_99,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_81])).

tff(c_36,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    r2_hidden('#skF_7',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_18])).

tff(c_78,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_71,c_75])).

tff(c_96,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_78])).

tff(c_105,plain,(
    k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_38])).

tff(c_125,plain,(
    k2_tarski('#skF_5','#skF_8') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_99,c_99,c_105])).

tff(c_135,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_18])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,(
    '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:36:46 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.21  
% 1.81/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.21  %$ r2_hidden > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 1.81/1.21  
% 1.81/1.21  %Foreground sorts:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Background operators:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Foreground operators:
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.81/1.21  tff('#skF_7', type, '#skF_7': $i).
% 1.81/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.81/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.81/1.21  tff('#skF_8', type, '#skF_8': $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.21  
% 1.96/1.22  tff(f_53, negated_conjecture, ~(![A, B, C, D]: ~(((k2_tarski(A, B) = k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_zfmisc_1)).
% 1.96/1.22  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.96/1.22  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.96/1.22  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.96/1.22  tff(c_34, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.96/1.22  tff(c_32, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.22  tff(c_38, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.96/1.22  tff(c_16, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.22  tff(c_68, plain, (r2_hidden('#skF_8', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_16])).
% 1.96/1.22  tff(c_75, plain, (![D_21, B_22, A_23]: (D_21=B_22 | D_21=A_23 | ~r2_hidden(D_21, k2_tarski(A_23, B_22)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.22  tff(c_81, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_68, c_75])).
% 1.96/1.22  tff(c_99, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_34, c_81])).
% 1.96/1.22  tff(c_36, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.96/1.22  tff(c_18, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.22  tff(c_71, plain, (r2_hidden('#skF_7', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_18])).
% 1.96/1.22  tff(c_78, plain, ('#skF_7'='#skF_6' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_71, c_75])).
% 1.96/1.22  tff(c_96, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_36, c_78])).
% 1.96/1.22  tff(c_105, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_38])).
% 1.96/1.22  tff(c_125, plain, (k2_tarski('#skF_5', '#skF_8')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_99, c_99, c_105])).
% 1.96/1.22  tff(c_135, plain, (r2_hidden('#skF_5', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_125, c_18])).
% 1.96/1.22  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.22  tff(c_142, plain, ('#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_135, c_2])).
% 1.96/1.22  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_142])).
% 1.96/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  Inference rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Ref     : 0
% 1.96/1.22  #Sup     : 27
% 1.96/1.22  #Fact    : 0
% 1.96/1.22  #Define  : 0
% 1.96/1.22  #Split   : 0
% 1.96/1.22  #Chain   : 0
% 1.96/1.22  #Close   : 0
% 1.96/1.22  
% 1.96/1.22  Ordering : KBO
% 1.96/1.22  
% 1.96/1.22  Simplification rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Subsume      : 3
% 1.96/1.22  #Demod        : 14
% 1.96/1.22  #Tautology    : 20
% 1.96/1.22  #SimpNegUnit  : 3
% 1.96/1.22  #BackRed      : 5
% 1.96/1.22  
% 1.96/1.22  #Partial instantiations: 0
% 1.96/1.22  #Strategies tried      : 1
% 1.96/1.22  
% 1.96/1.22  Timing (in seconds)
% 1.96/1.22  ----------------------
% 1.96/1.23  Preprocessing        : 0.35
% 1.96/1.23  Parsing              : 0.18
% 1.96/1.23  CNF conversion       : 0.03
% 1.96/1.23  Main loop            : 0.13
% 1.96/1.23  Inferencing          : 0.03
% 1.96/1.23  Reduction            : 0.05
% 1.96/1.23  Demodulation         : 0.03
% 1.96/1.23  BG Simplification    : 0.02
% 1.96/1.23  Subsumption          : 0.03
% 1.96/1.23  Abstraction          : 0.01
% 1.96/1.23  MUC search           : 0.00
% 1.96/1.23  Cooper               : 0.00
% 1.96/1.23  Total                : 0.50
% 1.96/1.23  Index Insertion      : 0.00
% 1.96/1.23  Index Deletion       : 0.00
% 1.96/1.23  Index Matching       : 0.00
% 1.96/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
