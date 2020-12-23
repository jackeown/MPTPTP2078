%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:18 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   30 (  34 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  37 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_32,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_70,plain,(
    ! [C_30,B_31,A_32] :
      ( r2_hidden(C_30,B_31)
      | ~ r2_hidden(C_30,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [D_43,B_44,B_45] :
      ( r2_hidden(D_43,B_44)
      | ~ r1_tarski(k2_tarski(D_43,B_45),B_44) ) ),
    inference(resolution,[status(thm)],[c_12,c_70])).

tff(c_147,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_134])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [D_40,B_41,A_42] :
      ( D_40 = B_41
      | D_40 = A_42
      | ~ r2_hidden(D_40,k2_tarski(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_167,plain,(
    ! [D_50,A_51] :
      ( D_50 = A_51
      | D_50 = A_51
      | ~ r2_hidden(D_50,k1_tarski(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_115])).

tff(c_170,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_147,c_167])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:33:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.20  
% 1.75/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.20  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.75/1.20  
% 1.75/1.20  %Foreground sorts:
% 1.75/1.20  
% 1.75/1.20  
% 1.75/1.20  %Background operators:
% 1.75/1.20  
% 1.75/1.20  
% 1.75/1.20  %Foreground operators:
% 1.75/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.75/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.75/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.75/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.75/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.75/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.75/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.75/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.75/1.20  
% 1.75/1.21  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.75/1.21  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.75/1.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.75/1.21  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.75/1.21  tff(c_32, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.75/1.21  tff(c_34, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.75/1.21  tff(c_12, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.75/1.21  tff(c_70, plain, (![C_30, B_31, A_32]: (r2_hidden(C_30, B_31) | ~r2_hidden(C_30, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.75/1.21  tff(c_134, plain, (![D_43, B_44, B_45]: (r2_hidden(D_43, B_44) | ~r1_tarski(k2_tarski(D_43, B_45), B_44))), inference(resolution, [status(thm)], [c_12, c_70])).
% 1.75/1.21  tff(c_147, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_134])).
% 1.75/1.21  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.75/1.21  tff(c_115, plain, (![D_40, B_41, A_42]: (D_40=B_41 | D_40=A_42 | ~r2_hidden(D_40, k2_tarski(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.75/1.21  tff(c_167, plain, (![D_50, A_51]: (D_50=A_51 | D_50=A_51 | ~r2_hidden(D_50, k1_tarski(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_115])).
% 1.75/1.21  tff(c_170, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_147, c_167])).
% 1.75/1.21  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_170])).
% 1.75/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.21  
% 1.75/1.21  Inference rules
% 1.75/1.21  ----------------------
% 1.75/1.21  #Ref     : 0
% 1.75/1.21  #Sup     : 32
% 1.75/1.21  #Fact    : 0
% 1.75/1.21  #Define  : 0
% 1.75/1.21  #Split   : 0
% 1.75/1.21  #Chain   : 0
% 1.75/1.21  #Close   : 0
% 1.75/1.21  
% 1.75/1.21  Ordering : KBO
% 1.75/1.21  
% 1.75/1.21  Simplification rules
% 1.75/1.21  ----------------------
% 1.75/1.21  #Subsume      : 2
% 1.75/1.21  #Demod        : 6
% 1.75/1.21  #Tautology    : 14
% 1.75/1.21  #SimpNegUnit  : 1
% 1.75/1.21  #BackRed      : 0
% 1.75/1.21  
% 1.75/1.21  #Partial instantiations: 0
% 1.75/1.21  #Strategies tried      : 1
% 1.75/1.21  
% 1.75/1.21  Timing (in seconds)
% 1.75/1.21  ----------------------
% 1.75/1.22  Preprocessing        : 0.30
% 1.75/1.22  Parsing              : 0.16
% 1.75/1.22  CNF conversion       : 0.02
% 1.75/1.22  Main loop            : 0.14
% 1.75/1.22  Inferencing          : 0.05
% 1.75/1.22  Reduction            : 0.04
% 1.75/1.22  Demodulation         : 0.03
% 1.75/1.22  BG Simplification    : 0.01
% 1.75/1.22  Subsumption          : 0.02
% 1.75/1.22  Abstraction          : 0.01
% 1.75/1.22  MUC search           : 0.00
% 1.75/1.22  Cooper               : 0.00
% 1.75/1.22  Total                : 0.45
% 1.75/1.22  Index Insertion      : 0.00
% 1.75/1.22  Index Deletion       : 0.00
% 1.75/1.22  Index Matching       : 0.00
% 1.75/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
