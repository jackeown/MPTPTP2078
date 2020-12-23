%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:01 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_30,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_121,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(k2_tarski(A_63,B_64),C_65)
      | ~ r2_hidden(B_64,C_65)
      | ~ r2_hidden(A_63,C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_137,plain,(
    ! [A_66,C_67] :
      ( r1_tarski(k1_tarski(A_66),C_67)
      | ~ r2_hidden(A_66,C_67)
      | ~ r2_hidden(A_66,C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_121])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_155,plain,(
    ! [A_73,C_74] :
      ( k2_xboole_0(k1_tarski(A_73),C_74) = C_74
      | ~ r2_hidden(A_73,C_74) ) ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_28,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_165,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_28])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:28:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.17  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.71/1.17  
% 1.71/1.17  %Foreground sorts:
% 1.71/1.17  
% 1.71/1.17  
% 1.71/1.17  %Background operators:
% 1.71/1.17  
% 1.71/1.17  
% 1.71/1.17  %Foreground operators:
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.71/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.71/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.71/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.71/1.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.71/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.71/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.71/1.17  
% 1.71/1.17  tff(f_58, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.71/1.17  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.71/1.17  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.71/1.17  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.71/1.17  tff(c_30, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.17  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.17  tff(c_121, plain, (![A_63, B_64, C_65]: (r1_tarski(k2_tarski(A_63, B_64), C_65) | ~r2_hidden(B_64, C_65) | ~r2_hidden(A_63, C_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.71/1.17  tff(c_137, plain, (![A_66, C_67]: (r1_tarski(k1_tarski(A_66), C_67) | ~r2_hidden(A_66, C_67) | ~r2_hidden(A_66, C_67))), inference(superposition, [status(thm), theory('equality')], [c_6, c_121])).
% 1.71/1.17  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.17  tff(c_155, plain, (![A_73, C_74]: (k2_xboole_0(k1_tarski(A_73), C_74)=C_74 | ~r2_hidden(A_73, C_74))), inference(resolution, [status(thm)], [c_137, c_2])).
% 1.71/1.17  tff(c_28, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.17  tff(c_165, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_155, c_28])).
% 1.71/1.17  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_165])).
% 1.71/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.17  
% 1.71/1.17  Inference rules
% 1.71/1.17  ----------------------
% 1.71/1.17  #Ref     : 0
% 1.71/1.17  #Sup     : 34
% 1.71/1.17  #Fact    : 0
% 1.71/1.17  #Define  : 0
% 1.71/1.17  #Split   : 0
% 1.71/1.17  #Chain   : 0
% 1.71/1.17  #Close   : 0
% 1.71/1.17  
% 1.71/1.17  Ordering : KBO
% 1.71/1.17  
% 1.71/1.17  Simplification rules
% 1.71/1.17  ----------------------
% 1.71/1.17  #Subsume      : 1
% 1.71/1.17  #Demod        : 1
% 1.71/1.17  #Tautology    : 22
% 1.71/1.17  #SimpNegUnit  : 0
% 1.71/1.17  #BackRed      : 0
% 1.71/1.17  
% 1.71/1.17  #Partial instantiations: 0
% 1.71/1.17  #Strategies tried      : 1
% 1.71/1.17  
% 1.71/1.17  Timing (in seconds)
% 1.71/1.17  ----------------------
% 1.71/1.18  Preprocessing        : 0.30
% 1.71/1.18  Parsing              : 0.16
% 1.71/1.18  CNF conversion       : 0.02
% 1.71/1.18  Main loop            : 0.12
% 1.71/1.18  Inferencing          : 0.05
% 1.71/1.18  Reduction            : 0.03
% 1.71/1.18  Demodulation         : 0.03
% 1.71/1.18  BG Simplification    : 0.01
% 1.71/1.18  Subsumption          : 0.02
% 1.71/1.18  Abstraction          : 0.01
% 1.71/1.18  MUC search           : 0.00
% 1.71/1.18  Cooper               : 0.00
% 1.71/1.18  Total                : 0.44
% 1.71/1.18  Index Insertion      : 0.00
% 1.71/1.18  Index Deletion       : 0.00
% 1.71/1.18  Index Matching       : 0.00
% 1.71/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
