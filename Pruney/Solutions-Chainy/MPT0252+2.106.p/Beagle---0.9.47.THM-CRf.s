%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:14 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_10,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13,plain,(
    ! [A_7,C_8,B_9] :
      ( r1_tarski(A_7,C_8)
      | ~ r1_tarski(k2_xboole_0(A_7,B_9),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_17,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_13])).

tff(c_23,plain,(
    ! [A_13,C_14,B_15] :
      ( r2_hidden(A_13,C_14)
      | ~ r1_tarski(k2_tarski(A_13,B_15),C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_17,c_23])).

tff(c_30,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.10  
% 1.57/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.11  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.57/1.11  
% 1.57/1.11  %Foreground sorts:
% 1.57/1.11  
% 1.57/1.11  
% 1.57/1.11  %Background operators:
% 1.57/1.11  
% 1.57/1.11  
% 1.57/1.11  %Foreground operators:
% 1.57/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.57/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.57/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.57/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.57/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.57/1.11  
% 1.57/1.11  tff(f_40, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.57/1.11  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.57/1.11  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.57/1.11  tff(c_10, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.57/1.11  tff(c_12, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.57/1.11  tff(c_13, plain, (![A_7, C_8, B_9]: (r1_tarski(A_7, C_8) | ~r1_tarski(k2_xboole_0(A_7, B_9), C_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.57/1.11  tff(c_17, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_12, c_13])).
% 1.57/1.11  tff(c_23, plain, (![A_13, C_14, B_15]: (r2_hidden(A_13, C_14) | ~r1_tarski(k2_tarski(A_13, B_15), C_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.57/1.11  tff(c_26, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_17, c_23])).
% 1.57/1.11  tff(c_30, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_26])).
% 1.57/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.11  
% 1.57/1.11  Inference rules
% 1.57/1.11  ----------------------
% 1.57/1.11  #Ref     : 0
% 1.57/1.11  #Sup     : 3
% 1.57/1.11  #Fact    : 0
% 1.57/1.11  #Define  : 0
% 1.57/1.11  #Split   : 0
% 1.57/1.11  #Chain   : 0
% 1.57/1.11  #Close   : 0
% 1.57/1.11  
% 1.57/1.11  Ordering : KBO
% 1.57/1.11  
% 1.57/1.11  Simplification rules
% 1.57/1.11  ----------------------
% 1.57/1.11  #Subsume      : 0
% 1.57/1.11  #Demod        : 0
% 1.57/1.11  #Tautology    : 0
% 1.57/1.11  #SimpNegUnit  : 1
% 1.57/1.11  #BackRed      : 0
% 1.57/1.11  
% 1.57/1.11  #Partial instantiations: 0
% 1.57/1.11  #Strategies tried      : 1
% 1.57/1.11  
% 1.57/1.11  Timing (in seconds)
% 1.57/1.11  ----------------------
% 1.57/1.11  Preprocessing        : 0.23
% 1.57/1.11  Parsing              : 0.12
% 1.57/1.12  CNF conversion       : 0.01
% 1.57/1.12  Main loop            : 0.06
% 1.57/1.12  Inferencing          : 0.03
% 1.57/1.12  Reduction            : 0.02
% 1.57/1.12  Demodulation         : 0.01
% 1.57/1.12  BG Simplification    : 0.01
% 1.57/1.12  Subsumption          : 0.01
% 1.57/1.12  Abstraction          : 0.00
% 1.57/1.12  MUC search           : 0.00
% 1.57/1.12  Cooper               : 0.00
% 1.57/1.12  Total                : 0.32
% 1.57/1.12  Index Insertion      : 0.00
% 1.57/1.12  Index Deletion       : 0.00
% 1.57/1.12  Index Matching       : 0.00
% 1.57/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
