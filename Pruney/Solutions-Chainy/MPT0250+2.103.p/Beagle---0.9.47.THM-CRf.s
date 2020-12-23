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
% DateTime   : Thu Dec  3 09:50:45 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_12,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_39,plain,(
    ! [A_16,C_17,B_18] :
      ( r1_tarski(A_16,C_17)
      | ~ r1_tarski(k2_xboole_0(A_16,B_18),C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_39])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | ~ r1_tarski(k1_tarski(A_7),B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_8])).

tff(c_50,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.63/1.15  
% 1.63/1.15  %Foreground sorts:
% 1.63/1.15  
% 1.63/1.15  
% 1.63/1.15  %Background operators:
% 1.63/1.15  
% 1.63/1.15  
% 1.63/1.15  %Foreground operators:
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.63/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.15  
% 1.63/1.15  tff(f_42, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.63/1.15  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.63/1.15  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.63/1.15  tff(c_12, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.15  tff(c_14, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.15  tff(c_39, plain, (![A_16, C_17, B_18]: (r1_tarski(A_16, C_17) | ~r1_tarski(k2_xboole_0(A_16, B_18), C_17))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.15  tff(c_43, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_14, c_39])).
% 1.63/1.15  tff(c_8, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | ~r1_tarski(k1_tarski(A_7), B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.15  tff(c_46, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_43, c_8])).
% 1.63/1.15  tff(c_50, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_46])).
% 1.63/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  Inference rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Ref     : 0
% 1.63/1.15  #Sup     : 7
% 1.63/1.15  #Fact    : 0
% 1.63/1.15  #Define  : 0
% 1.63/1.15  #Split   : 0
% 1.63/1.15  #Chain   : 0
% 1.63/1.15  #Close   : 0
% 1.63/1.15  
% 1.63/1.15  Ordering : KBO
% 1.63/1.15  
% 1.63/1.15  Simplification rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Subsume      : 0
% 1.63/1.15  #Demod        : 0
% 1.63/1.16  #Tautology    : 5
% 1.63/1.16  #SimpNegUnit  : 1
% 1.63/1.16  #BackRed      : 0
% 1.63/1.16  
% 1.63/1.16  #Partial instantiations: 0
% 1.63/1.16  #Strategies tried      : 1
% 1.63/1.16  
% 1.63/1.16  Timing (in seconds)
% 1.63/1.16  ----------------------
% 1.63/1.16  Preprocessing        : 0.29
% 1.63/1.16  Parsing              : 0.15
% 1.63/1.16  CNF conversion       : 0.02
% 1.63/1.16  Main loop            : 0.07
% 1.63/1.16  Inferencing          : 0.03
% 1.63/1.16  Reduction            : 0.02
% 1.63/1.16  Demodulation         : 0.01
% 1.63/1.16  BG Simplification    : 0.01
% 1.63/1.16  Subsumption          : 0.01
% 1.63/1.16  Abstraction          : 0.01
% 1.63/1.16  MUC search           : 0.00
% 1.63/1.16  Cooper               : 0.00
% 1.63/1.16  Total                : 0.38
% 1.63/1.16  Index Insertion      : 0.00
% 1.63/1.16  Index Deletion       : 0.00
% 1.63/1.16  Index Matching       : 0.00
% 1.63/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
