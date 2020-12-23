%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:36 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  26 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_30,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_127,plain,(
    ! [C_45,B_46] :
      ( r2_hidden(C_45,B_46)
      | ~ r1_tarski(k1_tarski(C_45),B_46) ) ),
    inference(resolution,[status(thm)],[c_14,c_117])).

tff(c_142,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_32,c_127])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_147,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_142,c_12])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:19:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.15  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.66/1.15  
% 1.66/1.15  %Foreground sorts:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Background operators:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Foreground operators:
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.66/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.66/1.15  tff('#skF_6', type, '#skF_6': $i).
% 1.66/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.66/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.66/1.15  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.66/1.15  
% 1.66/1.15  tff(f_56, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.66/1.15  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.66/1.15  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.66/1.15  tff(c_30, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.66/1.15  tff(c_32, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.66/1.15  tff(c_14, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.66/1.15  tff(c_117, plain, (![C_42, B_43, A_44]: (r2_hidden(C_42, B_43) | ~r2_hidden(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.66/1.15  tff(c_127, plain, (![C_45, B_46]: (r2_hidden(C_45, B_46) | ~r1_tarski(k1_tarski(C_45), B_46))), inference(resolution, [status(thm)], [c_14, c_117])).
% 1.66/1.15  tff(c_142, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_127])).
% 1.66/1.15  tff(c_12, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.66/1.15  tff(c_147, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_142, c_12])).
% 1.66/1.15  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_147])).
% 1.66/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  Inference rules
% 1.66/1.15  ----------------------
% 1.66/1.15  #Ref     : 0
% 1.66/1.15  #Sup     : 25
% 1.66/1.15  #Fact    : 0
% 1.66/1.15  #Define  : 0
% 1.66/1.15  #Split   : 0
% 1.66/1.15  #Chain   : 0
% 1.66/1.15  #Close   : 0
% 1.66/1.15  
% 1.66/1.15  Ordering : KBO
% 1.66/1.15  
% 1.66/1.15  Simplification rules
% 1.66/1.15  ----------------------
% 1.66/1.15  #Subsume      : 1
% 1.66/1.15  #Demod        : 2
% 1.66/1.15  #Tautology    : 12
% 1.66/1.15  #SimpNegUnit  : 3
% 1.66/1.15  #BackRed      : 0
% 1.66/1.15  
% 1.66/1.15  #Partial instantiations: 0
% 1.66/1.15  #Strategies tried      : 1
% 1.66/1.15  
% 1.66/1.15  Timing (in seconds)
% 1.66/1.15  ----------------------
% 1.66/1.16  Preprocessing        : 0.28
% 1.66/1.16  Parsing              : 0.15
% 1.66/1.16  CNF conversion       : 0.02
% 1.66/1.16  Main loop            : 0.11
% 1.66/1.16  Inferencing          : 0.04
% 1.66/1.16  Reduction            : 0.03
% 1.66/1.16  Demodulation         : 0.02
% 1.66/1.16  BG Simplification    : 0.01
% 1.66/1.16  Subsumption          : 0.02
% 1.66/1.16  Abstraction          : 0.01
% 1.66/1.16  MUC search           : 0.00
% 1.66/1.16  Cooper               : 0.00
% 1.66/1.16  Total                : 0.41
% 1.66/1.16  Index Insertion      : 0.00
% 1.66/1.16  Index Deletion       : 0.00
% 1.66/1.16  Index Matching       : 0.00
% 1.66/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
