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
% DateTime   : Thu Dec  3 09:47:51 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_50,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_123,plain,(
    ! [B_49,A_50] : k2_xboole_0(B_49,A_50) = k2_xboole_0(A_50,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_138,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_52])).

tff(c_999,plain,(
    ! [A_89,B_90] :
      ( r2_hidden(A_89,B_90)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_89),B_90),B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1014,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_3'))
    | ~ r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_999])).

tff(c_1031,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1014])).

tff(c_28,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1034,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1031,c_28])).

tff(c_1038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.37  
% 2.68/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.37  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.68/1.37  
% 2.68/1.37  %Foreground sorts:
% 2.68/1.37  
% 2.68/1.37  
% 2.68/1.37  %Background operators:
% 2.68/1.37  
% 2.68/1.37  
% 2.68/1.37  %Foreground operators:
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.68/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.68/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.68/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.37  
% 2.68/1.38  tff(f_79, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.68/1.38  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.68/1.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.68/1.38  tff(f_74, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 2.68/1.38  tff(f_62, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.68/1.38  tff(c_50, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.38  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.38  tff(c_123, plain, (![B_49, A_50]: (k2_xboole_0(B_49, A_50)=k2_xboole_0(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.38  tff(c_52, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.38  tff(c_138, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_123, c_52])).
% 2.68/1.38  tff(c_999, plain, (![A_89, B_90]: (r2_hidden(A_89, B_90) | ~r1_tarski(k2_xboole_0(k1_tarski(A_89), B_90), B_90))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.68/1.38  tff(c_1014, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3')) | ~r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_999])).
% 2.68/1.38  tff(c_1031, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1014])).
% 2.68/1.38  tff(c_28, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.68/1.38  tff(c_1034, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1031, c_28])).
% 2.68/1.38  tff(c_1038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1034])).
% 2.68/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.38  
% 2.68/1.38  Inference rules
% 2.68/1.38  ----------------------
% 2.68/1.38  #Ref     : 0
% 2.68/1.38  #Sup     : 234
% 2.68/1.38  #Fact    : 0
% 2.68/1.38  #Define  : 0
% 2.68/1.38  #Split   : 1
% 2.68/1.38  #Chain   : 0
% 2.68/1.38  #Close   : 0
% 2.68/1.38  
% 2.68/1.38  Ordering : KBO
% 2.68/1.38  
% 2.68/1.38  Simplification rules
% 2.68/1.38  ----------------------
% 2.68/1.38  #Subsume      : 1
% 2.68/1.38  #Demod        : 120
% 2.68/1.38  #Tautology    : 186
% 2.68/1.38  #SimpNegUnit  : 1
% 2.68/1.38  #BackRed      : 0
% 2.68/1.38  
% 2.68/1.38  #Partial instantiations: 0
% 2.68/1.38  #Strategies tried      : 1
% 2.68/1.38  
% 2.68/1.38  Timing (in seconds)
% 2.68/1.38  ----------------------
% 2.68/1.38  Preprocessing        : 0.32
% 2.68/1.38  Parsing              : 0.17
% 2.68/1.38  CNF conversion       : 0.02
% 2.68/1.38  Main loop            : 0.32
% 2.68/1.38  Inferencing          : 0.11
% 2.68/1.38  Reduction            : 0.12
% 2.68/1.38  Demodulation         : 0.09
% 2.68/1.38  BG Simplification    : 0.02
% 2.68/1.38  Subsumption          : 0.05
% 2.68/1.38  Abstraction          : 0.02
% 2.68/1.39  MUC search           : 0.00
% 2.68/1.39  Cooper               : 0.00
% 2.68/1.39  Total                : 0.66
% 2.68/1.39  Index Insertion      : 0.00
% 2.68/1.39  Index Deletion       : 0.00
% 2.68/1.39  Index Matching       : 0.00
% 2.68/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
