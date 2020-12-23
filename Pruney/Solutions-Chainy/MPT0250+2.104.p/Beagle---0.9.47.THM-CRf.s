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
% DateTime   : Thu Dec  3 09:50:45 EST 2020

% Result     : Theorem 1.41s
% Output     : CNFRefutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   16 (  17 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_34,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

tff(c_4,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_3),B_4),B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_7])).

tff(c_14,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:34:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.41/1.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.41/1.01  
% 1.41/1.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.41/1.02  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.41/1.02  
% 1.41/1.02  %Foreground sorts:
% 1.41/1.02  
% 1.41/1.02  
% 1.41/1.02  %Background operators:
% 1.41/1.02  
% 1.41/1.02  
% 1.41/1.02  %Foreground operators:
% 1.41/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.41/1.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.41/1.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.41/1.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.41/1.02  tff('#skF_2', type, '#skF_2': $i).
% 1.41/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.41/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.41/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.41/1.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.41/1.02  
% 1.41/1.03  tff(f_34, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.41/1.03  tff(f_29, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 1.41/1.03  tff(c_4, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.41/1.03  tff(c_6, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.41/1.03  tff(c_7, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | ~r1_tarski(k2_xboole_0(k1_tarski(A_3), B_4), B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.41/1.03  tff(c_10, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_7])).
% 1.41/1.03  tff(c_14, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_10])).
% 1.41/1.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.41/1.03  
% 1.41/1.03  Inference rules
% 1.41/1.03  ----------------------
% 1.41/1.03  #Ref     : 0
% 1.41/1.03  #Sup     : 1
% 1.41/1.03  #Fact    : 0
% 1.41/1.03  #Define  : 0
% 1.41/1.03  #Split   : 0
% 1.41/1.03  #Chain   : 0
% 1.41/1.03  #Close   : 0
% 1.41/1.03  
% 1.41/1.03  Ordering : KBO
% 1.41/1.03  
% 1.41/1.03  Simplification rules
% 1.41/1.03  ----------------------
% 1.41/1.03  #Subsume      : 0
% 1.41/1.03  #Demod        : 0
% 1.41/1.03  #Tautology    : 0
% 1.41/1.03  #SimpNegUnit  : 1
% 1.41/1.03  #BackRed      : 0
% 1.41/1.03  
% 1.41/1.03  #Partial instantiations: 0
% 1.41/1.03  #Strategies tried      : 1
% 1.41/1.03  
% 1.41/1.03  Timing (in seconds)
% 1.41/1.03  ----------------------
% 1.41/1.03  Preprocessing        : 0.24
% 1.41/1.03  Parsing              : 0.14
% 1.41/1.03  CNF conversion       : 0.01
% 1.41/1.03  Main loop            : 0.05
% 1.41/1.03  Inferencing          : 0.02
% 1.41/1.03  Reduction            : 0.01
% 1.41/1.03  Demodulation         : 0.01
% 1.41/1.03  BG Simplification    : 0.00
% 1.41/1.03  Subsumption          : 0.00
% 1.41/1.03  Abstraction          : 0.00
% 1.41/1.03  MUC search           : 0.00
% 1.41/1.03  Cooper               : 0.00
% 1.41/1.03  Total                : 0.31
% 1.41/1.03  Index Insertion      : 0.00
% 1.41/1.03  Index Deletion       : 0.00
% 1.41/1.03  Index Matching       : 0.00
% 1.41/1.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
