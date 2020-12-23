%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:45 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_30,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_238,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_315,plain,(
    ! [A_83] :
      ( r1_tarski(A_83,'#skF_2')
      | ~ r1_tarski(A_83,k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_32,c_238])).

tff(c_325,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_315])).

tff(c_14,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,(
    ! [A_49,C_50,B_51] :
      ( r2_hidden(A_49,C_50)
      | ~ r1_tarski(k2_tarski(A_49,B_51),C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_114,plain,(
    ! [A_22,C_50] :
      ( r2_hidden(A_22,C_50)
      | ~ r1_tarski(k1_tarski(A_22),C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_103])).

tff(c_330,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_325,c_114])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.64  
% 2.55/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.65  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.55/1.65  
% 2.55/1.65  %Foreground sorts:
% 2.55/1.65  
% 2.55/1.65  
% 2.55/1.65  %Background operators:
% 2.55/1.65  
% 2.55/1.65  
% 2.55/1.65  %Foreground operators:
% 2.55/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.55/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.55/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.55/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.55/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.65  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.55/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.55/1.65  
% 2.55/1.66  tff(f_62, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.55/1.66  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.55/1.66  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.55/1.66  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.55/1.66  tff(f_57, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.55/1.66  tff(c_30, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.55/1.66  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.55/1.66  tff(c_32, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.55/1.66  tff(c_238, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.66  tff(c_315, plain, (![A_83]: (r1_tarski(A_83, '#skF_2') | ~r1_tarski(A_83, k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')))), inference(resolution, [status(thm)], [c_32, c_238])).
% 2.55/1.66  tff(c_325, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_4, c_315])).
% 2.55/1.66  tff(c_14, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.66  tff(c_103, plain, (![A_49, C_50, B_51]: (r2_hidden(A_49, C_50) | ~r1_tarski(k2_tarski(A_49, B_51), C_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.55/1.66  tff(c_114, plain, (![A_22, C_50]: (r2_hidden(A_22, C_50) | ~r1_tarski(k1_tarski(A_22), C_50))), inference(superposition, [status(thm), theory('equality')], [c_14, c_103])).
% 2.55/1.66  tff(c_330, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_325, c_114])).
% 2.55/1.66  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_330])).
% 2.55/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.66  
% 2.55/1.66  Inference rules
% 2.55/1.66  ----------------------
% 2.55/1.66  #Ref     : 0
% 2.55/1.66  #Sup     : 67
% 2.55/1.66  #Fact    : 0
% 2.55/1.66  #Define  : 0
% 2.55/1.66  #Split   : 0
% 2.55/1.66  #Chain   : 0
% 2.55/1.66  #Close   : 0
% 2.55/1.66  
% 2.55/1.66  Ordering : KBO
% 2.55/1.66  
% 2.55/1.66  Simplification rules
% 2.55/1.66  ----------------------
% 2.55/1.66  #Subsume      : 2
% 2.55/1.66  #Demod        : 19
% 2.55/1.66  #Tautology    : 39
% 2.55/1.66  #SimpNegUnit  : 1
% 2.55/1.66  #BackRed      : 0
% 2.55/1.66  
% 2.55/1.66  #Partial instantiations: 0
% 2.55/1.66  #Strategies tried      : 1
% 2.55/1.66  
% 2.55/1.66  Timing (in seconds)
% 2.55/1.66  ----------------------
% 2.55/1.67  Preprocessing        : 0.49
% 2.55/1.67  Parsing              : 0.26
% 2.55/1.67  CNF conversion       : 0.03
% 2.55/1.67  Main loop            : 0.32
% 2.55/1.67  Inferencing          : 0.13
% 2.55/1.67  Reduction            : 0.11
% 2.55/1.67  Demodulation         : 0.09
% 2.55/1.67  BG Simplification    : 0.02
% 2.55/1.67  Subsumption          : 0.05
% 2.55/1.67  Abstraction          : 0.02
% 2.55/1.67  MUC search           : 0.00
% 2.55/1.67  Cooper               : 0.00
% 2.55/1.67  Total                : 0.85
% 2.55/1.67  Index Insertion      : 0.00
% 2.55/1.67  Index Deletion       : 0.00
% 2.55/1.67  Index Matching       : 0.00
% 2.55/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
