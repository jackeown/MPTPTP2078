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
% DateTime   : Thu Dec  3 09:47:46 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  31 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_48,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_42,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [D_16,B_12] : r2_hidden(D_16,k2_tarski(D_16,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_1'(A_32,B_33),A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_151,plain,(
    ! [A_51,B_52] :
      ( '#skF_1'(k1_tarski(A_51),B_52) = A_51
      | r1_tarski(k1_tarski(A_51),B_52) ) ),
    inference(resolution,[status(thm)],[c_79,c_8])).

tff(c_159,plain,(
    '#skF_1'(k1_tarski('#skF_6'),k2_tarski('#skF_6','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_151,c_42])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_166,plain,
    ( ~ r2_hidden('#skF_6',k2_tarski('#skF_6','#skF_7'))
    | r1_tarski(k1_tarski('#skF_6'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_4])).

tff(c_172,plain,(
    r1_tarski(k1_tarski('#skF_6'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_166])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.17  
% 1.82/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.17  %$ r2_hidden > r1_tarski > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1
% 1.82/1.17  
% 1.82/1.17  %Foreground sorts:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Background operators:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Foreground operators:
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.82/1.17  tff('#skF_7', type, '#skF_7': $i).
% 1.82/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.82/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.17  tff('#skF_6', type, '#skF_6': $i).
% 1.82/1.17  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.82/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.17  
% 1.82/1.18  tff(f_55, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.82/1.18  tff(f_48, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.82/1.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.82/1.18  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.82/1.18  tff(c_42, plain, (~r1_tarski(k1_tarski('#skF_6'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.82/1.18  tff(c_24, plain, (![D_16, B_12]: (r2_hidden(D_16, k2_tarski(D_16, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.82/1.18  tff(c_79, plain, (![A_32, B_33]: (r2_hidden('#skF_1'(A_32, B_33), A_32) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.18  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.82/1.18  tff(c_151, plain, (![A_51, B_52]: ('#skF_1'(k1_tarski(A_51), B_52)=A_51 | r1_tarski(k1_tarski(A_51), B_52))), inference(resolution, [status(thm)], [c_79, c_8])).
% 1.82/1.18  tff(c_159, plain, ('#skF_1'(k1_tarski('#skF_6'), k2_tarski('#skF_6', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_151, c_42])).
% 1.82/1.18  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.18  tff(c_166, plain, (~r2_hidden('#skF_6', k2_tarski('#skF_6', '#skF_7')) | r1_tarski(k1_tarski('#skF_6'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_4])).
% 1.82/1.18  tff(c_172, plain, (r1_tarski(k1_tarski('#skF_6'), k2_tarski('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_166])).
% 1.82/1.18  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_172])).
% 1.82/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.18  
% 1.82/1.18  Inference rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Ref     : 0
% 1.82/1.18  #Sup     : 28
% 1.82/1.18  #Fact    : 0
% 1.82/1.18  #Define  : 0
% 1.82/1.18  #Split   : 0
% 1.82/1.18  #Chain   : 0
% 1.82/1.18  #Close   : 0
% 1.82/1.18  
% 1.82/1.18  Ordering : KBO
% 1.82/1.18  
% 1.82/1.18  Simplification rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Subsume      : 3
% 1.82/1.18  #Demod        : 7
% 1.82/1.18  #Tautology    : 14
% 1.82/1.18  #SimpNegUnit  : 2
% 1.82/1.18  #BackRed      : 0
% 1.82/1.18  
% 1.82/1.18  #Partial instantiations: 0
% 1.82/1.18  #Strategies tried      : 1
% 1.82/1.18  
% 1.82/1.18  Timing (in seconds)
% 1.82/1.18  ----------------------
% 1.82/1.18  Preprocessing        : 0.29
% 1.82/1.18  Parsing              : 0.14
% 1.82/1.18  CNF conversion       : 0.02
% 1.82/1.18  Main loop            : 0.14
% 1.82/1.18  Inferencing          : 0.05
% 1.82/1.18  Reduction            : 0.04
% 1.82/1.18  Demodulation         : 0.03
% 1.82/1.18  BG Simplification    : 0.01
% 1.82/1.18  Subsumption          : 0.03
% 1.82/1.18  Abstraction          : 0.01
% 1.82/1.18  MUC search           : 0.00
% 1.82/1.18  Cooper               : 0.00
% 1.82/1.18  Total                : 0.44
% 1.82/1.18  Index Insertion      : 0.00
% 1.82/1.18  Index Deletion       : 0.00
% 1.82/1.18  Index Matching       : 0.00
% 1.82/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
