%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:04 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   16 (  17 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(c_6,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ! [B_7,A_8] :
      ( r2_hidden(B_7,A_8)
      | k3_xboole_0(A_8,k1_tarski(B_7)) != k1_tarski(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_28])).

tff(c_35,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.33  % CPULimit   : 60
% 0.19/0.33  % DateTime   : Tue Dec  1 10:34:06 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.05  
% 1.48/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.06  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.48/1.06  
% 1.48/1.06  %Foreground sorts:
% 1.48/1.06  
% 1.48/1.06  
% 1.48/1.06  %Background operators:
% 1.48/1.06  
% 1.48/1.06  
% 1.48/1.06  %Foreground operators:
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.48/1.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.48/1.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.48/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.48/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.48/1.06  
% 1.48/1.06  tff(f_36, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 1.48/1.06  tff(f_31, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 1.48/1.06  tff(c_6, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.48/1.06  tff(c_8, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.48/1.06  tff(c_28, plain, (![B_7, A_8]: (r2_hidden(B_7, A_8) | k3_xboole_0(A_8, k1_tarski(B_7))!=k1_tarski(B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.48/1.06  tff(c_31, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_28])).
% 1.48/1.06  tff(c_35, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_31])).
% 1.48/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.06  
% 1.48/1.06  Inference rules
% 1.48/1.06  ----------------------
% 1.48/1.06  #Ref     : 0
% 1.48/1.06  #Sup     : 7
% 1.48/1.06  #Fact    : 0
% 1.48/1.06  #Define  : 0
% 1.48/1.06  #Split   : 0
% 1.48/1.06  #Chain   : 0
% 1.48/1.06  #Close   : 0
% 1.48/1.06  
% 1.48/1.06  Ordering : KBO
% 1.48/1.06  
% 1.48/1.06  Simplification rules
% 1.48/1.06  ----------------------
% 1.48/1.06  #Subsume      : 0
% 1.48/1.06  #Demod        : 0
% 1.48/1.06  #Tautology    : 4
% 1.48/1.06  #SimpNegUnit  : 1
% 1.48/1.06  #BackRed      : 0
% 1.48/1.06  
% 1.48/1.06  #Partial instantiations: 0
% 1.48/1.06  #Strategies tried      : 1
% 1.48/1.06  
% 1.48/1.06  Timing (in seconds)
% 1.48/1.06  ----------------------
% 1.48/1.06  Preprocessing        : 0.25
% 1.48/1.06  Parsing              : 0.14
% 1.48/1.06  CNF conversion       : 0.01
% 1.48/1.06  Main loop            : 0.07
% 1.48/1.07  Inferencing          : 0.04
% 1.48/1.07  Reduction            : 0.02
% 1.48/1.07  Demodulation         : 0.01
% 1.48/1.07  BG Simplification    : 0.01
% 1.48/1.07  Subsumption          : 0.01
% 1.48/1.07  Abstraction          : 0.00
% 1.48/1.07  MUC search           : 0.00
% 1.48/1.07  Cooper               : 0.00
% 1.48/1.07  Total                : 0.34
% 1.48/1.07  Index Insertion      : 0.00
% 1.48/1.07  Index Deletion       : 0.00
% 1.48/1.07  Index Matching       : 0.00
% 1.48/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
