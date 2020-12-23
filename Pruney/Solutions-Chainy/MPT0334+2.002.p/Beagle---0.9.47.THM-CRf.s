%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:51 EST 2020

% Result     : Theorem 4.39s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  30 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_70,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_54,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(k1_tarski(A_38),B_39)
      | r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3174,plain,(
    ! [C_2180,B_2181,A_2182] :
      ( k4_xboole_0(k2_xboole_0(C_2180,B_2181),A_2182) = k2_xboole_0(k4_xboole_0(C_2180,A_2182),B_2181)
      | ~ r1_xboole_0(A_2182,B_2181) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    k4_xboole_0(k2_xboole_0('#skF_7',k1_tarski('#skF_5')),k1_tarski('#skF_6')) != k2_xboole_0(k4_xboole_0('#skF_7',k1_tarski('#skF_6')),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_71,plain,(
    k4_xboole_0(k2_xboole_0('#skF_7',k1_tarski('#skF_5')),k1_tarski('#skF_6')) != k2_xboole_0(k1_tarski('#skF_5'),k4_xboole_0('#skF_7',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_3258,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_7',k1_tarski('#skF_6')),k1_tarski('#skF_5')) != k2_xboole_0(k1_tarski('#skF_5'),k4_xboole_0('#skF_7',k1_tarski('#skF_6')))
    | ~ r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3174,c_71])).

tff(c_3332,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3258])).

tff(c_3355,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_3332])).

tff(c_34,plain,(
    ! [C_27,A_23] :
      ( C_27 = A_23
      | ~ r2_hidden(C_27,k1_tarski(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3360,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3355,c_34])).

tff(c_3400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:21:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.39/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.89  
% 4.39/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.89  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.39/1.89  
% 4.39/1.89  %Foreground sorts:
% 4.39/1.89  
% 4.39/1.89  
% 4.39/1.89  %Background operators:
% 4.39/1.89  
% 4.39/1.89  
% 4.39/1.89  %Foreground operators:
% 4.39/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.39/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.39/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.39/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.39/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.39/1.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.39/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.39/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.39/1.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.39/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.39/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.39/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.39/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.39/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.39/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.39/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.39/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.39/1.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.39/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.39/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.39/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.39/1.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.39/1.89  
% 4.39/1.90  tff(f_91, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 4.39/1.90  tff(f_71, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.39/1.90  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.39/1.90  tff(f_49, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 4.39/1.90  tff(f_58, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.39/1.90  tff(c_70, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.39/1.90  tff(c_54, plain, (![A_38, B_39]: (r1_xboole_0(k1_tarski(A_38), B_39) | r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.39/1.90  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.39/1.90  tff(c_3174, plain, (![C_2180, B_2181, A_2182]: (k4_xboole_0(k2_xboole_0(C_2180, B_2181), A_2182)=k2_xboole_0(k4_xboole_0(C_2180, A_2182), B_2181) | ~r1_xboole_0(A_2182, B_2181))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.39/1.90  tff(c_68, plain, (k4_xboole_0(k2_xboole_0('#skF_7', k1_tarski('#skF_5')), k1_tarski('#skF_6'))!=k2_xboole_0(k4_xboole_0('#skF_7', k1_tarski('#skF_6')), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.39/1.90  tff(c_71, plain, (k4_xboole_0(k2_xboole_0('#skF_7', k1_tarski('#skF_5')), k1_tarski('#skF_6'))!=k2_xboole_0(k1_tarski('#skF_5'), k4_xboole_0('#skF_7', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_68])).
% 4.39/1.90  tff(c_3258, plain, (k2_xboole_0(k4_xboole_0('#skF_7', k1_tarski('#skF_6')), k1_tarski('#skF_5'))!=k2_xboole_0(k1_tarski('#skF_5'), k4_xboole_0('#skF_7', k1_tarski('#skF_6'))) | ~r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3174, c_71])).
% 4.39/1.90  tff(c_3332, plain, (~r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3258])).
% 4.39/1.90  tff(c_3355, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_3332])).
% 4.39/1.90  tff(c_34, plain, (![C_27, A_23]: (C_27=A_23 | ~r2_hidden(C_27, k1_tarski(A_23)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.39/1.90  tff(c_3360, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_3355, c_34])).
% 4.39/1.90  tff(c_3400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_3360])).
% 4.39/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.90  
% 4.39/1.90  Inference rules
% 4.39/1.90  ----------------------
% 4.39/1.90  #Ref     : 0
% 4.39/1.90  #Sup     : 636
% 4.39/1.90  #Fact    : 0
% 4.39/1.90  #Define  : 0
% 4.39/1.90  #Split   : 2
% 4.39/1.90  #Chain   : 0
% 4.39/1.90  #Close   : 0
% 4.39/1.90  
% 4.39/1.90  Ordering : KBO
% 4.39/1.90  
% 4.39/1.90  Simplification rules
% 4.39/1.90  ----------------------
% 4.39/1.90  #Subsume      : 92
% 4.39/1.90  #Demod        : 414
% 4.39/1.90  #Tautology    : 210
% 4.39/1.90  #SimpNegUnit  : 3
% 4.39/1.90  #BackRed      : 1
% 4.39/1.90  
% 4.39/1.90  #Partial instantiations: 1037
% 4.39/1.90  #Strategies tried      : 1
% 4.39/1.90  
% 4.39/1.90  Timing (in seconds)
% 4.39/1.90  ----------------------
% 4.39/1.90  Preprocessing        : 0.35
% 4.39/1.90  Parsing              : 0.18
% 4.39/1.90  CNF conversion       : 0.02
% 4.39/1.90  Main loop            : 0.73
% 4.39/1.90  Inferencing          : 0.27
% 4.39/1.90  Reduction            : 0.28
% 4.39/1.90  Demodulation         : 0.23
% 4.39/1.90  BG Simplification    : 0.03
% 4.39/1.90  Subsumption          : 0.11
% 4.39/1.90  Abstraction          : 0.03
% 4.39/1.90  MUC search           : 0.00
% 4.39/1.90  Cooper               : 0.00
% 4.39/1.90  Total                : 1.10
% 4.39/1.90  Index Insertion      : 0.00
% 4.39/1.90  Index Deletion       : 0.00
% 4.39/1.90  Index Matching       : 0.00
% 4.39/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
