%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:52 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_344,plain,(
    ! [A_47,B_48] :
      ( r2_hidden(A_47,B_48)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_47),B_48),B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_357,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_3'))
    | ~ r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_344])).

tff(c_372,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_357])).

tff(c_14,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_375,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_372,c_14])).

tff(c_379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:21:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.18  
% 2.03/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.18  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.03/1.18  
% 2.03/1.18  %Foreground sorts:
% 2.03/1.18  
% 2.03/1.18  
% 2.03/1.18  %Background operators:
% 2.03/1.18  
% 2.03/1.18  
% 2.03/1.18  %Foreground operators:
% 2.03/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.18  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.18  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.03/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.18  
% 2.03/1.19  tff(f_63, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.03/1.19  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.03/1.19  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.03/1.19  tff(f_56, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 2.03/1.19  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.03/1.19  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.03/1.19  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.03/1.19  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.03/1.19  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.19  tff(c_107, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2])).
% 2.03/1.19  tff(c_344, plain, (![A_47, B_48]: (r2_hidden(A_47, B_48) | ~r1_tarski(k2_xboole_0(k1_tarski(A_47), B_48), B_48))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.19  tff(c_357, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3')) | ~r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_344])).
% 2.03/1.19  tff(c_372, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_357])).
% 2.03/1.19  tff(c_14, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.03/1.19  tff(c_375, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_372, c_14])).
% 2.03/1.19  tff(c_379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_375])).
% 2.03/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.19  
% 2.03/1.19  Inference rules
% 2.03/1.19  ----------------------
% 2.03/1.19  #Ref     : 0
% 2.03/1.19  #Sup     : 86
% 2.03/1.19  #Fact    : 0
% 2.03/1.19  #Define  : 0
% 2.03/1.19  #Split   : 0
% 2.03/1.19  #Chain   : 0
% 2.03/1.19  #Close   : 0
% 2.03/1.19  
% 2.03/1.19  Ordering : KBO
% 2.03/1.19  
% 2.03/1.19  Simplification rules
% 2.03/1.19  ----------------------
% 2.03/1.19  #Subsume      : 0
% 2.03/1.19  #Demod        : 29
% 2.03/1.19  #Tautology    : 64
% 2.03/1.19  #SimpNegUnit  : 1
% 2.03/1.19  #BackRed      : 0
% 2.03/1.19  
% 2.03/1.19  #Partial instantiations: 0
% 2.03/1.19  #Strategies tried      : 1
% 2.03/1.19  
% 2.03/1.19  Timing (in seconds)
% 2.03/1.19  ----------------------
% 2.03/1.20  Preprocessing        : 0.30
% 2.03/1.20  Parsing              : 0.16
% 2.03/1.20  CNF conversion       : 0.02
% 2.03/1.20  Main loop            : 0.19
% 2.03/1.20  Inferencing          : 0.06
% 2.03/1.20  Reduction            : 0.07
% 2.03/1.20  Demodulation         : 0.05
% 2.03/1.20  BG Simplification    : 0.01
% 2.03/1.20  Subsumption          : 0.03
% 2.03/1.20  Abstraction          : 0.01
% 2.03/1.20  MUC search           : 0.00
% 2.03/1.20  Cooper               : 0.00
% 2.03/1.20  Total                : 0.51
% 2.03/1.20  Index Insertion      : 0.00
% 2.03/1.20  Index Deletion       : 0.00
% 2.03/1.20  Index Matching       : 0.00
% 2.03/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
