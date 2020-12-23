%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:09 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   15 (  16 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),B)
          & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_4,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6,plain,(
    r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_7,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden(A_3,B_4)
      | ~ r1_xboole_0(k1_tarski(A_3),B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_7])).

tff(c_14,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.02  
% 1.49/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.03  %$ r2_hidden > r1_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.55/1.03  
% 1.55/1.03  %Foreground sorts:
% 1.55/1.03  
% 1.55/1.03  
% 1.55/1.03  %Background operators:
% 1.55/1.03  
% 1.55/1.03  
% 1.55/1.03  %Foreground operators:
% 1.55/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.55/1.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.55/1.03  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.55/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.03  
% 1.55/1.04  tff(f_36, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 1.55/1.04  tff(f_30, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.55/1.04  tff(c_4, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.55/1.04  tff(c_6, plain, (r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.55/1.04  tff(c_7, plain, (![A_3, B_4]: (~r2_hidden(A_3, B_4) | ~r1_xboole_0(k1_tarski(A_3), B_4))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.55/1.04  tff(c_10, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_7])).
% 1.55/1.04  tff(c_14, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.55/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.04  
% 1.55/1.04  Inference rules
% 1.55/1.04  ----------------------
% 1.55/1.04  #Ref     : 0
% 1.55/1.04  #Sup     : 1
% 1.55/1.04  #Fact    : 0
% 1.55/1.04  #Define  : 0
% 1.55/1.04  #Split   : 0
% 1.55/1.04  #Chain   : 0
% 1.55/1.04  #Close   : 0
% 1.55/1.04  
% 1.55/1.04  Ordering : KBO
% 1.55/1.04  
% 1.55/1.04  Simplification rules
% 1.55/1.04  ----------------------
% 1.55/1.04  #Subsume      : 0
% 1.55/1.04  #Demod        : 1
% 1.55/1.04  #Tautology    : 0
% 1.55/1.04  #SimpNegUnit  : 0
% 1.55/1.04  #BackRed      : 0
% 1.55/1.04  
% 1.55/1.04  #Partial instantiations: 0
% 1.55/1.04  #Strategies tried      : 1
% 1.55/1.04  
% 1.55/1.04  Timing (in seconds)
% 1.55/1.04  ----------------------
% 1.55/1.04  Preprocessing        : 0.23
% 1.55/1.04  Parsing              : 0.13
% 1.55/1.04  CNF conversion       : 0.01
% 1.55/1.05  Main loop            : 0.05
% 1.55/1.05  Inferencing          : 0.02
% 1.55/1.05  Reduction            : 0.01
% 1.55/1.05  Demodulation         : 0.01
% 1.55/1.05  BG Simplification    : 0.01
% 1.55/1.05  Subsumption          : 0.00
% 1.55/1.05  Abstraction          : 0.00
% 1.55/1.05  MUC search           : 0.00
% 1.55/1.05  Cooper               : 0.00
% 1.55/1.05  Total                : 0.31
% 1.55/1.05  Index Insertion      : 0.00
% 1.55/1.05  Index Deletion       : 0.00
% 1.55/1.05  Index Matching       : 0.00
% 1.55/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
