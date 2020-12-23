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
% DateTime   : Thu Dec  3 09:51:22 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_130,plain,(
    ! [A_33,B_34] :
      ( ~ r2_hidden(A_33,B_34)
      | ~ r1_xboole_0(k1_tarski(A_33),B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_138,plain,(
    ! [A_33] : ~ r2_hidden(A_33,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_32,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_57,plain,(
    ! [A_26,B_27] :
      ( k1_xboole_0 = A_26
      | k2_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_57])).

tff(c_12,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_12])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:58:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.15  
% 1.72/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.15  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.72/1.15  
% 1.72/1.15  %Foreground sorts:
% 1.72/1.15  
% 1.72/1.15  
% 1.72/1.15  %Background operators:
% 1.72/1.15  
% 1.72/1.15  
% 1.72/1.15  %Foreground operators:
% 1.72/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.72/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.72/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.72/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.72/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.15  
% 1.72/1.16  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.72/1.16  tff(f_53, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.72/1.16  tff(f_59, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.72/1.16  tff(f_29, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.72/1.16  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.72/1.16  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.72/1.16  tff(c_130, plain, (![A_33, B_34]: (~r2_hidden(A_33, B_34) | ~r1_xboole_0(k1_tarski(A_33), B_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.72/1.16  tff(c_138, plain, (![A_33]: (~r2_hidden(A_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_130])).
% 1.72/1.16  tff(c_32, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.72/1.16  tff(c_57, plain, (![A_26, B_27]: (k1_xboole_0=A_26 | k2_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.72/1.16  tff(c_64, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_32, c_57])).
% 1.72/1.16  tff(c_12, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.72/1.16  tff(c_69, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_64, c_12])).
% 1.72/1.16  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_69])).
% 1.72/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  
% 1.72/1.16  Inference rules
% 1.72/1.16  ----------------------
% 1.72/1.16  #Ref     : 0
% 1.72/1.16  #Sup     : 27
% 1.72/1.16  #Fact    : 0
% 1.72/1.16  #Define  : 0
% 1.72/1.16  #Split   : 0
% 1.72/1.16  #Chain   : 0
% 1.72/1.16  #Close   : 0
% 1.72/1.16  
% 1.72/1.16  Ordering : KBO
% 1.72/1.16  
% 1.72/1.16  Simplification rules
% 1.72/1.16  ----------------------
% 1.72/1.16  #Subsume      : 1
% 1.72/1.16  #Demod        : 1
% 1.72/1.16  #Tautology    : 22
% 1.72/1.16  #SimpNegUnit  : 1
% 1.72/1.16  #BackRed      : 2
% 1.72/1.16  
% 1.72/1.16  #Partial instantiations: 0
% 1.72/1.16  #Strategies tried      : 1
% 1.72/1.16  
% 1.72/1.16  Timing (in seconds)
% 1.72/1.16  ----------------------
% 1.72/1.16  Preprocessing        : 0.30
% 1.72/1.16  Parsing              : 0.16
% 1.72/1.16  CNF conversion       : 0.02
% 1.72/1.16  Main loop            : 0.10
% 1.72/1.16  Inferencing          : 0.03
% 1.72/1.16  Reduction            : 0.04
% 1.72/1.16  Demodulation         : 0.03
% 1.72/1.16  BG Simplification    : 0.01
% 1.72/1.16  Subsumption          : 0.02
% 1.72/1.16  Abstraction          : 0.01
% 1.72/1.16  MUC search           : 0.00
% 1.72/1.16  Cooper               : 0.00
% 1.72/1.16  Total                : 0.42
% 1.72/1.16  Index Insertion      : 0.00
% 1.72/1.16  Index Deletion       : 0.00
% 1.72/1.16  Index Matching       : 0.00
% 1.72/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
