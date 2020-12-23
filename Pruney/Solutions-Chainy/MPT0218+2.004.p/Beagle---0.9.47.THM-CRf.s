%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:46 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  35 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_58,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_78,plain,(
    ! [A_59,B_60] : k1_enumset1(A_59,A_59,B_60) = k2_tarski(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,(
    ! [A_59,B_60] : r2_hidden(A_59,k2_tarski(A_59,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_12])).

tff(c_108,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_187,plain,(
    ! [A_88,B_89] :
      ( '#skF_1'(k1_tarski(A_88),B_89) = A_88
      | r1_tarski(k1_tarski(A_88),B_89) ) ),
    inference(resolution,[status(thm)],[c_108,c_32])).

tff(c_195,plain,(
    '#skF_1'(k1_tarski('#skF_6'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_187,c_58])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_202,plain,
    ( ~ r2_hidden('#skF_6',k2_tarski('#skF_6','#skF_7'))
    | r1_tarski(k1_tarski('#skF_6'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_4])).

tff(c_208,plain,(
    r1_tarski(k1_tarski('#skF_6'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_202])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.22  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.03/1.22  
% 2.03/1.22  %Foreground sorts:
% 2.03/1.22  
% 2.03/1.22  
% 2.03/1.22  %Background operators:
% 2.03/1.22  
% 2.03/1.22  
% 2.03/1.22  %Foreground operators:
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.22  tff('#skF_7', type, '#skF_7': $i).
% 2.03/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.03/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.03/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.03/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.22  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.03/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.03/1.22  
% 2.03/1.23  tff(f_71, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.03/1.23  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.03/1.23  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.03/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.03/1.23  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.03/1.23  tff(c_58, plain, (~r1_tarski(k1_tarski('#skF_6'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.03/1.23  tff(c_78, plain, (![A_59, B_60]: (k1_enumset1(A_59, A_59, B_60)=k2_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.03/1.23  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.23  tff(c_87, plain, (![A_59, B_60]: (r2_hidden(A_59, k2_tarski(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_12])).
% 2.03/1.23  tff(c_108, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), A_67) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.23  tff(c_32, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.03/1.23  tff(c_187, plain, (![A_88, B_89]: ('#skF_1'(k1_tarski(A_88), B_89)=A_88 | r1_tarski(k1_tarski(A_88), B_89))), inference(resolution, [status(thm)], [c_108, c_32])).
% 2.03/1.23  tff(c_195, plain, ('#skF_1'(k1_tarski('#skF_6'), k2_tarski('#skF_6', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_187, c_58])).
% 2.03/1.23  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.23  tff(c_202, plain, (~r2_hidden('#skF_6', k2_tarski('#skF_6', '#skF_7')) | r1_tarski(k1_tarski('#skF_6'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_4])).
% 2.03/1.23  tff(c_208, plain, (r1_tarski(k1_tarski('#skF_6'), k2_tarski('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_202])).
% 2.03/1.23  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_208])).
% 2.03/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.23  
% 2.03/1.23  Inference rules
% 2.03/1.23  ----------------------
% 2.03/1.23  #Ref     : 0
% 2.03/1.23  #Sup     : 34
% 2.03/1.23  #Fact    : 0
% 2.03/1.23  #Define  : 0
% 2.03/1.23  #Split   : 0
% 2.03/1.23  #Chain   : 0
% 2.03/1.23  #Close   : 0
% 2.03/1.23  
% 2.03/1.23  Ordering : KBO
% 2.03/1.23  
% 2.03/1.23  Simplification rules
% 2.03/1.23  ----------------------
% 2.03/1.23  #Subsume      : 2
% 2.03/1.23  #Demod        : 8
% 2.03/1.23  #Tautology    : 17
% 2.03/1.23  #SimpNegUnit  : 2
% 2.03/1.23  #BackRed      : 0
% 2.03/1.23  
% 2.03/1.23  #Partial instantiations: 0
% 2.03/1.23  #Strategies tried      : 1
% 2.03/1.23  
% 2.03/1.23  Timing (in seconds)
% 2.03/1.23  ----------------------
% 2.12/1.23  Preprocessing        : 0.32
% 2.12/1.23  Parsing              : 0.16
% 2.12/1.23  CNF conversion       : 0.03
% 2.12/1.23  Main loop            : 0.15
% 2.12/1.23  Inferencing          : 0.05
% 2.12/1.23  Reduction            : 0.05
% 2.12/1.23  Demodulation         : 0.04
% 2.12/1.23  BG Simplification    : 0.02
% 2.12/1.23  Subsumption          : 0.03
% 2.12/1.23  Abstraction          : 0.01
% 2.12/1.23  MUC search           : 0.00
% 2.12/1.23  Cooper               : 0.00
% 2.12/1.23  Total                : 0.49
% 2.12/1.23  Index Insertion      : 0.00
% 2.12/1.23  Index Deletion       : 0.00
% 2.12/1.23  Index Matching       : 0.00
% 2.12/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
