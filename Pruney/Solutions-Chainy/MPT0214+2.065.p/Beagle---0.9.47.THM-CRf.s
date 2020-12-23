%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:38 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  26 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_22,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    ! [C_20,B_21,A_22] :
      ( r2_hidden(C_20,B_21)
      | ~ r2_hidden(C_20,A_22)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [C_23,B_24] :
      ( r2_hidden(C_23,B_24)
      | ~ r1_tarski(k1_tarski(C_23),B_24) ) ),
    inference(resolution,[status(thm)],[c_10,c_45])).

tff(c_62,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_52])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62,c_8])).

tff(c_72,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.17  
% 1.72/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.18  %$ r2_hidden > r1_tarski > k6_enumset1 > #nlpp > k1_tarski > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 1.72/1.18  
% 1.72/1.18  %Foreground sorts:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Background operators:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Foreground operators:
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.72/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.72/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.72/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.18  
% 1.72/1.18  tff(f_46, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.72/1.18  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.72/1.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.72/1.18  tff(c_22, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.72/1.18  tff(c_24, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.72/1.18  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.18  tff(c_45, plain, (![C_20, B_21, A_22]: (r2_hidden(C_20, B_21) | ~r2_hidden(C_20, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.72/1.18  tff(c_52, plain, (![C_23, B_24]: (r2_hidden(C_23, B_24) | ~r1_tarski(k1_tarski(C_23), B_24))), inference(resolution, [status(thm)], [c_10, c_45])).
% 1.72/1.18  tff(c_62, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_52])).
% 1.72/1.18  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.18  tff(c_67, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_62, c_8])).
% 1.72/1.18  tff(c_72, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_67])).
% 1.72/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.18  
% 1.72/1.18  Inference rules
% 1.72/1.18  ----------------------
% 1.72/1.18  #Ref     : 0
% 1.72/1.18  #Sup     : 9
% 1.72/1.18  #Fact    : 0
% 1.72/1.18  #Define  : 0
% 1.72/1.18  #Split   : 0
% 1.72/1.18  #Chain   : 0
% 1.72/1.18  #Close   : 0
% 1.72/1.18  
% 1.72/1.18  Ordering : KBO
% 1.72/1.18  
% 1.72/1.18  Simplification rules
% 1.72/1.18  ----------------------
% 1.72/1.18  #Subsume      : 0
% 1.72/1.18  #Demod        : 1
% 1.72/1.18  #Tautology    : 2
% 1.72/1.18  #SimpNegUnit  : 1
% 1.72/1.18  #BackRed      : 0
% 1.72/1.18  
% 1.72/1.18  #Partial instantiations: 0
% 1.72/1.18  #Strategies tried      : 1
% 1.72/1.18  
% 1.72/1.18  Timing (in seconds)
% 1.72/1.18  ----------------------
% 1.72/1.18  Preprocessing        : 0.29
% 1.72/1.18  Parsing              : 0.15
% 1.72/1.18  CNF conversion       : 0.02
% 1.72/1.18  Main loop            : 0.08
% 1.72/1.18  Inferencing          : 0.03
% 1.72/1.18  Reduction            : 0.02
% 1.72/1.18  Demodulation         : 0.02
% 1.72/1.19  BG Simplification    : 0.01
% 1.72/1.19  Subsumption          : 0.02
% 1.72/1.19  Abstraction          : 0.00
% 1.72/1.19  MUC search           : 0.00
% 1.72/1.19  Cooper               : 0.00
% 1.72/1.19  Total                : 0.39
% 1.72/1.19  Index Insertion      : 0.00
% 1.72/1.19  Index Deletion       : 0.00
% 1.72/1.19  Index Matching       : 0.00
% 1.72/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
