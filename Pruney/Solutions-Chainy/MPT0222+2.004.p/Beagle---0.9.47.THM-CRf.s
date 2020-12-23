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
% DateTime   : Thu Dec  3 09:48:16 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_22,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(k1_tarski(A_16),B_17)
      | r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_43,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_39,c_20])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_50,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:47:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.06  
% 1.54/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.06  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.54/1.06  
% 1.54/1.06  %Foreground sorts:
% 1.54/1.06  
% 1.54/1.06  
% 1.54/1.06  %Background operators:
% 1.54/1.06  
% 1.54/1.06  
% 1.54/1.06  %Foreground operators:
% 1.54/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.54/1.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.54/1.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.54/1.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.54/1.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.54/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.54/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.06  tff('#skF_4', type, '#skF_4': $i).
% 1.54/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.54/1.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.54/1.06  
% 1.61/1.07  tff(f_47, negated_conjecture, ~(![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.61/1.07  tff(f_41, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.61/1.07  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.61/1.07  tff(c_22, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.61/1.07  tff(c_39, plain, (![A_16, B_17]: (r1_xboole_0(k1_tarski(A_16), B_17) | r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.61/1.07  tff(c_20, plain, (~r1_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.61/1.07  tff(c_43, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_39, c_20])).
% 1.61/1.07  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.61/1.07  tff(c_46, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_43, c_2])).
% 1.61/1.07  tff(c_50, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_46])).
% 1.61/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.07  
% 1.61/1.07  Inference rules
% 1.61/1.07  ----------------------
% 1.61/1.07  #Ref     : 0
% 1.61/1.07  #Sup     : 5
% 1.61/1.07  #Fact    : 0
% 1.61/1.07  #Define  : 0
% 1.61/1.07  #Split   : 0
% 1.61/1.07  #Chain   : 0
% 1.61/1.07  #Close   : 0
% 1.61/1.07  
% 1.61/1.07  Ordering : KBO
% 1.61/1.07  
% 1.61/1.07  Simplification rules
% 1.61/1.07  ----------------------
% 1.61/1.07  #Subsume      : 0
% 1.61/1.07  #Demod        : 0
% 1.61/1.07  #Tautology    : 3
% 1.61/1.07  #SimpNegUnit  : 1
% 1.61/1.07  #BackRed      : 0
% 1.61/1.07  
% 1.61/1.07  #Partial instantiations: 0
% 1.61/1.07  #Strategies tried      : 1
% 1.61/1.07  
% 1.61/1.07  Timing (in seconds)
% 1.61/1.07  ----------------------
% 1.61/1.07  Preprocessing        : 0.26
% 1.61/1.07  Parsing              : 0.13
% 1.61/1.07  CNF conversion       : 0.02
% 1.61/1.07  Main loop            : 0.07
% 1.61/1.07  Inferencing          : 0.02
% 1.61/1.07  Reduction            : 0.02
% 1.61/1.07  Demodulation         : 0.01
% 1.61/1.07  BG Simplification    : 0.01
% 1.61/1.07  Subsumption          : 0.01
% 1.61/1.07  Abstraction          : 0.00
% 1.61/1.07  MUC search           : 0.00
% 1.61/1.07  Cooper               : 0.00
% 1.61/1.07  Total                : 0.35
% 1.61/1.07  Index Insertion      : 0.00
% 1.61/1.07  Index Deletion       : 0.00
% 1.61/1.07  Index Matching       : 0.00
% 1.61/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
