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
% DateTime   : Thu Dec  3 09:49:17 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   25 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_64,plain,(
    '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_95,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [E_15,A_9,C_11] : r2_hidden(E_15,k1_enumset1(A_9,E_15,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,(
    ! [A_42,B_43] : r2_hidden(A_42,k2_tarski(A_42,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_26])).

tff(c_66,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_86,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_9')) = k2_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_86])).

tff(c_124,plain,(
    ! [D_48,B_49,A_50] :
      ( r2_hidden(D_48,B_49)
      | ~ r2_hidden(D_48,k3_xboole_0(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_141,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_57,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_124])).

tff(c_150,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_104,c_141])).

tff(c_46,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_154,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_150,c_46])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 1.95/1.19  
% 1.95/1.19  %Foreground sorts:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Background operators:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Foreground operators:
% 1.95/1.19  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.95/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.19  tff('#skF_7', type, '#skF_7': $i).
% 1.95/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.19  tff('#skF_9', type, '#skF_9': $i).
% 1.95/1.19  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.95/1.19  tff('#skF_8', type, '#skF_8': $i).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.95/1.19  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.95/1.19  
% 1.95/1.20  tff(f_71, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.95/1.20  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.95/1.20  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.95/1.20  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.95/1.20  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.95/1.20  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.95/1.20  tff(c_64, plain, ('#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.95/1.20  tff(c_95, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.95/1.20  tff(c_26, plain, (![E_15, A_9, C_11]: (r2_hidden(E_15, k1_enumset1(A_9, E_15, C_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.20  tff(c_104, plain, (![A_42, B_43]: (r2_hidden(A_42, k2_tarski(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_26])).
% 1.95/1.20  tff(c_66, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.95/1.20  tff(c_86, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.95/1.20  tff(c_90, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_9'))=k2_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_66, c_86])).
% 1.95/1.20  tff(c_124, plain, (![D_48, B_49, A_50]: (r2_hidden(D_48, B_49) | ~r2_hidden(D_48, k3_xboole_0(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.95/1.20  tff(c_141, plain, (![D_57]: (r2_hidden(D_57, k1_tarski('#skF_9')) | ~r2_hidden(D_57, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_124])).
% 1.95/1.20  tff(c_150, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_104, c_141])).
% 1.95/1.20  tff(c_46, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.95/1.20  tff(c_154, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_150, c_46])).
% 1.95/1.20  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_154])).
% 1.95/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  Inference rules
% 1.95/1.20  ----------------------
% 1.95/1.20  #Ref     : 0
% 1.95/1.20  #Sup     : 20
% 1.95/1.20  #Fact    : 0
% 1.95/1.20  #Define  : 0
% 1.95/1.20  #Split   : 0
% 1.95/1.20  #Chain   : 0
% 1.95/1.20  #Close   : 0
% 1.95/1.20  
% 1.95/1.20  Ordering : KBO
% 1.95/1.20  
% 1.95/1.20  Simplification rules
% 1.95/1.20  ----------------------
% 1.95/1.20  #Subsume      : 0
% 1.95/1.20  #Demod        : 3
% 1.95/1.20  #Tautology    : 13
% 1.95/1.20  #SimpNegUnit  : 1
% 1.95/1.20  #BackRed      : 0
% 1.95/1.20  
% 1.95/1.20  #Partial instantiations: 0
% 1.95/1.20  #Strategies tried      : 1
% 1.95/1.20  
% 1.95/1.20  Timing (in seconds)
% 1.95/1.20  ----------------------
% 1.95/1.20  Preprocessing        : 0.30
% 1.95/1.20  Parsing              : 0.15
% 1.95/1.20  CNF conversion       : 0.02
% 1.95/1.20  Main loop            : 0.14
% 1.95/1.20  Inferencing          : 0.04
% 1.95/1.20  Reduction            : 0.05
% 1.95/1.20  Demodulation         : 0.04
% 1.95/1.20  BG Simplification    : 0.02
% 1.95/1.20  Subsumption          : 0.03
% 1.95/1.20  Abstraction          : 0.01
% 1.95/1.20  MUC search           : 0.00
% 1.95/1.20  Cooper               : 0.00
% 1.95/1.20  Total                : 0.46
% 1.95/1.21  Index Insertion      : 0.00
% 1.95/1.21  Index Deletion       : 0.00
% 1.95/1.21  Index Matching       : 0.00
% 1.95/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
