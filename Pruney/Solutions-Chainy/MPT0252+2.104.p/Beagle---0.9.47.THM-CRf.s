%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:13 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_28,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_160,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(A_67,C_68)
      | ~ r1_tarski(B_69,C_68)
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,'#skF_3')
      | ~ r1_tarski(A_73,k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_160])).

tff(c_191,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_181])).

tff(c_26,plain,(
    ! [A_38,C_40,B_39] :
      ( r2_hidden(A_38,C_40)
      | ~ r1_tarski(k2_tarski(A_38,B_39),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_196,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_191,c_26])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:14:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.28  
% 1.93/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.28  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.93/1.28  
% 1.93/1.28  %Foreground sorts:
% 1.93/1.28  
% 1.93/1.28  
% 1.93/1.28  %Background operators:
% 1.93/1.28  
% 1.93/1.28  
% 1.93/1.28  %Foreground operators:
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.28  
% 1.93/1.29  tff(f_60, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.93/1.29  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.93/1.29  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.93/1.29  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.93/1.29  tff(c_28, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.93/1.29  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.29  tff(c_30, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.93/1.29  tff(c_160, plain, (![A_67, C_68, B_69]: (r1_tarski(A_67, C_68) | ~r1_tarski(B_69, C_68) | ~r1_tarski(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.29  tff(c_181, plain, (![A_73]: (r1_tarski(A_73, '#skF_3') | ~r1_tarski(A_73, k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')))), inference(resolution, [status(thm)], [c_30, c_160])).
% 1.93/1.29  tff(c_191, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_4, c_181])).
% 1.93/1.29  tff(c_26, plain, (![A_38, C_40, B_39]: (r2_hidden(A_38, C_40) | ~r1_tarski(k2_tarski(A_38, B_39), C_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.29  tff(c_196, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_191, c_26])).
% 1.93/1.29  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_196])).
% 1.93/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.29  
% 1.93/1.29  Inference rules
% 1.93/1.29  ----------------------
% 1.93/1.29  #Ref     : 0
% 1.93/1.29  #Sup     : 38
% 1.93/1.29  #Fact    : 0
% 1.93/1.29  #Define  : 0
% 1.93/1.29  #Split   : 0
% 1.93/1.29  #Chain   : 0
% 1.93/1.29  #Close   : 0
% 1.93/1.29  
% 1.93/1.29  Ordering : KBO
% 1.93/1.29  
% 1.93/1.29  Simplification rules
% 1.93/1.29  ----------------------
% 1.93/1.29  #Subsume      : 0
% 1.93/1.29  #Demod        : 7
% 1.93/1.29  #Tautology    : 25
% 1.93/1.29  #SimpNegUnit  : 1
% 1.93/1.29  #BackRed      : 0
% 1.93/1.29  
% 1.93/1.29  #Partial instantiations: 0
% 1.93/1.29  #Strategies tried      : 1
% 1.93/1.29  
% 1.93/1.29  Timing (in seconds)
% 1.93/1.29  ----------------------
% 1.93/1.29  Preprocessing        : 0.33
% 1.93/1.29  Parsing              : 0.18
% 1.93/1.29  CNF conversion       : 0.02
% 1.93/1.29  Main loop            : 0.14
% 1.93/1.29  Inferencing          : 0.05
% 1.93/1.29  Reduction            : 0.04
% 1.93/1.29  Demodulation         : 0.03
% 1.93/1.29  BG Simplification    : 0.01
% 1.93/1.29  Subsumption          : 0.02
% 1.93/1.29  Abstraction          : 0.01
% 1.93/1.29  MUC search           : 0.00
% 1.93/1.29  Cooper               : 0.00
% 1.93/1.29  Total                : 0.49
% 1.93/1.29  Index Insertion      : 0.00
% 1.93/1.29  Index Deletion       : 0.00
% 1.93/1.29  Index Matching       : 0.00
% 1.93/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
