%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:56 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  26 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_42,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    r1_tarski(k1_tarski('#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [C_41,B_42] :
      ( r2_hidden(C_41,B_42)
      | ~ r1_tarski(k1_tarski(C_41),B_42) ) ),
    inference(resolution,[status(thm)],[c_10,c_112])).

tff(c_135,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_44,c_125])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_140,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_135,c_8])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:45:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.18  %$ r2_hidden > r1_tarski > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1
% 1.83/1.18  
% 1.83/1.18  %Foreground sorts:
% 1.83/1.18  
% 1.83/1.18  
% 1.83/1.18  %Background operators:
% 1.83/1.18  
% 1.83/1.18  
% 1.83/1.18  %Foreground operators:
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.83/1.18  tff('#skF_7', type, '#skF_7': $i).
% 1.83/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.83/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.83/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.83/1.18  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.83/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.83/1.18  
% 1.83/1.19  tff(f_57, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 1.83/1.19  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.83/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.83/1.19  tff(c_42, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.83/1.19  tff(c_44, plain, (r1_tarski(k1_tarski('#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.83/1.19  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.83/1.19  tff(c_112, plain, (![C_38, B_39, A_40]: (r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.19  tff(c_125, plain, (![C_41, B_42]: (r2_hidden(C_41, B_42) | ~r1_tarski(k1_tarski(C_41), B_42))), inference(resolution, [status(thm)], [c_10, c_112])).
% 1.83/1.19  tff(c_135, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_44, c_125])).
% 1.83/1.19  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.83/1.19  tff(c_140, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_135, c_8])).
% 1.83/1.19  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_140])).
% 1.83/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  Inference rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Ref     : 0
% 1.83/1.19  #Sup     : 21
% 1.83/1.19  #Fact    : 0
% 1.83/1.19  #Define  : 0
% 1.83/1.19  #Split   : 0
% 1.83/1.19  #Chain   : 0
% 1.83/1.19  #Close   : 0
% 1.83/1.19  
% 1.83/1.19  Ordering : KBO
% 1.83/1.19  
% 1.83/1.19  Simplification rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Subsume      : 1
% 1.83/1.19  #Demod        : 3
% 1.83/1.19  #Tautology    : 10
% 1.83/1.19  #SimpNegUnit  : 1
% 1.83/1.19  #BackRed      : 0
% 1.83/1.19  
% 1.83/1.19  #Partial instantiations: 0
% 1.83/1.19  #Strategies tried      : 1
% 1.83/1.19  
% 1.83/1.19  Timing (in seconds)
% 1.83/1.19  ----------------------
% 1.83/1.19  Preprocessing        : 0.31
% 1.83/1.19  Parsing              : 0.15
% 1.83/1.19  CNF conversion       : 0.02
% 1.83/1.19  Main loop            : 0.13
% 1.83/1.19  Inferencing          : 0.04
% 1.83/1.19  Reduction            : 0.04
% 1.83/1.19  Demodulation         : 0.03
% 1.83/1.19  BG Simplification    : 0.02
% 1.83/1.19  Subsumption          : 0.03
% 1.83/1.19  Abstraction          : 0.01
% 1.83/1.19  MUC search           : 0.00
% 1.83/1.19  Cooper               : 0.00
% 1.83/1.19  Total                : 0.46
% 1.83/1.19  Index Insertion      : 0.00
% 1.83/1.19  Index Deletion       : 0.00
% 1.83/1.19  Index Matching       : 0.00
% 1.83/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
