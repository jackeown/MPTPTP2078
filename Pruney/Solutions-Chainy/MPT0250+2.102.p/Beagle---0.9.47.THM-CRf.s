%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:45 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_18,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_100,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_tarski(A_32,C_33)
      | ~ r1_tarski(B_34,C_33)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_146,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,'#skF_2')
      | ~ r1_tarski(A_43,k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_20,c_100])).

tff(c_161,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_146])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | ~ r1_tarski(k1_tarski(A_12),B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_166,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_161,c_12])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.34  
% 2.06/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.34  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.06/1.34  
% 2.06/1.34  %Foreground sorts:
% 2.06/1.34  
% 2.06/1.34  
% 2.06/1.34  %Background operators:
% 2.06/1.34  
% 2.06/1.34  
% 2.06/1.34  %Foreground operators:
% 2.06/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.34  
% 2.06/1.35  tff(f_50, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.06/1.35  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.06/1.35  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.06/1.35  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.06/1.35  tff(c_18, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.35  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.35  tff(c_20, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.35  tff(c_100, plain, (![A_32, C_33, B_34]: (r1_tarski(A_32, C_33) | ~r1_tarski(B_34, C_33) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.35  tff(c_146, plain, (![A_43]: (r1_tarski(A_43, '#skF_2') | ~r1_tarski(A_43, k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')))), inference(resolution, [status(thm)], [c_20, c_100])).
% 2.06/1.35  tff(c_161, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_4, c_146])).
% 2.06/1.35  tff(c_12, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | ~r1_tarski(k1_tarski(A_12), B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.06/1.35  tff(c_166, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_161, c_12])).
% 2.06/1.35  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_166])).
% 2.06/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.35  
% 2.06/1.35  Inference rules
% 2.06/1.35  ----------------------
% 2.06/1.35  #Ref     : 0
% 2.06/1.35  #Sup     : 34
% 2.06/1.35  #Fact    : 0
% 2.06/1.35  #Define  : 0
% 2.06/1.35  #Split   : 0
% 2.06/1.35  #Chain   : 0
% 2.06/1.35  #Close   : 0
% 2.06/1.35  
% 2.06/1.35  Ordering : KBO
% 2.06/1.35  
% 2.06/1.35  Simplification rules
% 2.06/1.35  ----------------------
% 2.06/1.35  #Subsume      : 2
% 2.06/1.35  #Demod        : 2
% 2.06/1.35  #Tautology    : 15
% 2.06/1.35  #SimpNegUnit  : 1
% 2.06/1.35  #BackRed      : 0
% 2.06/1.35  
% 2.06/1.35  #Partial instantiations: 0
% 2.06/1.35  #Strategies tried      : 1
% 2.06/1.35  
% 2.06/1.35  Timing (in seconds)
% 2.06/1.35  ----------------------
% 2.06/1.35  Preprocessing        : 0.34
% 2.06/1.35  Parsing              : 0.18
% 2.06/1.35  CNF conversion       : 0.02
% 2.06/1.35  Main loop            : 0.17
% 2.06/1.35  Inferencing          : 0.07
% 2.06/1.35  Reduction            : 0.05
% 2.06/1.35  Demodulation         : 0.04
% 2.06/1.35  BG Simplification    : 0.01
% 2.06/1.35  Subsumption          : 0.02
% 2.06/1.35  Abstraction          : 0.01
% 2.06/1.35  MUC search           : 0.00
% 2.06/1.35  Cooper               : 0.00
% 2.06/1.35  Total                : 0.54
% 2.06/1.35  Index Insertion      : 0.00
% 2.06/1.35  Index Deletion       : 0.00
% 2.06/1.35  Index Matching       : 0.00
% 2.06/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
