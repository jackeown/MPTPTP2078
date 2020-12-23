%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:11 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_39,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(k1_tarski(A_7),B_8) = k1_xboole_0
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_12])).

tff(c_38,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(k1_tarski(A_11),B_12) = k1_tarski(A_11)
      | r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_68,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.14  
% 1.60/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.15  %$ r2_hidden > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.60/1.15  
% 1.60/1.15  %Foreground sorts:
% 1.60/1.15  
% 1.60/1.15  
% 1.60/1.15  %Background operators:
% 1.60/1.15  
% 1.60/1.15  
% 1.60/1.15  %Foreground operators:
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.15  
% 1.60/1.16  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 1.60/1.16  tff(f_39, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 1.60/1.16  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.60/1.16  tff(c_14, plain, (![A_7, B_8]: (k4_xboole_0(k1_tarski(A_7), B_8)=k1_xboole_0 | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.60/1.16  tff(c_12, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.60/1.16  tff(c_32, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_12])).
% 1.60/1.16  tff(c_38, plain, (![A_11, B_12]: (k4_xboole_0(k1_tarski(A_11), B_12)=k1_tarski(A_11) | r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.60/1.16  tff(c_10, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.60/1.16  tff(c_53, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_38, c_10])).
% 1.60/1.16  tff(c_68, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_53])).
% 1.60/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  Inference rules
% 1.60/1.16  ----------------------
% 1.60/1.16  #Ref     : 0
% 1.60/1.16  #Sup     : 14
% 1.60/1.16  #Fact    : 0
% 1.60/1.16  #Define  : 0
% 1.60/1.16  #Split   : 0
% 1.60/1.16  #Chain   : 0
% 1.60/1.16  #Close   : 0
% 1.60/1.16  
% 1.60/1.16  Ordering : KBO
% 1.60/1.16  
% 1.60/1.16  Simplification rules
% 1.60/1.16  ----------------------
% 1.60/1.16  #Subsume      : 1
% 1.60/1.16  #Demod        : 0
% 1.60/1.16  #Tautology    : 6
% 1.60/1.16  #SimpNegUnit  : 1
% 1.60/1.16  #BackRed      : 0
% 1.60/1.16  
% 1.60/1.16  #Partial instantiations: 0
% 1.60/1.16  #Strategies tried      : 1
% 1.60/1.16  
% 1.60/1.16  Timing (in seconds)
% 1.60/1.16  ----------------------
% 1.60/1.16  Preprocessing        : 0.27
% 1.60/1.16  Parsing              : 0.15
% 1.60/1.16  CNF conversion       : 0.02
% 1.60/1.16  Main loop            : 0.07
% 1.60/1.16  Inferencing          : 0.04
% 1.60/1.16  Reduction            : 0.01
% 1.60/1.16  Demodulation         : 0.00
% 1.60/1.16  BG Simplification    : 0.01
% 1.60/1.16  Subsumption          : 0.01
% 1.60/1.16  Abstraction          : 0.00
% 1.60/1.16  MUC search           : 0.00
% 1.60/1.16  Cooper               : 0.00
% 1.60/1.16  Total                : 0.37
% 1.60/1.16  Index Insertion      : 0.00
% 1.60/1.16  Index Deletion       : 0.00
% 1.60/1.16  Index Matching       : 0.00
% 1.60/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
