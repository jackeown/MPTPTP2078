%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:06 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
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
        ( r2_hidden(A,B)
       => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_8,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [B_7,A_8] :
      ( k3_xboole_0(B_7,k1_tarski(A_8)) = k1_tarski(A_8)
      | ~ r2_hidden(A_8,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6])).

tff(c_38,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:49:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.05  
% 1.49/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.06  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.49/1.06  
% 1.49/1.06  %Foreground sorts:
% 1.49/1.06  
% 1.49/1.06  
% 1.49/1.06  %Background operators:
% 1.49/1.06  
% 1.49/1.06  
% 1.49/1.06  %Foreground operators:
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.49/1.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.49/1.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.49/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.49/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.49/1.06  
% 1.49/1.06  tff(f_36, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 1.49/1.06  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 1.49/1.06  tff(c_8, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.49/1.06  tff(c_24, plain, (![B_7, A_8]: (k3_xboole_0(B_7, k1_tarski(A_8))=k1_tarski(A_8) | ~r2_hidden(A_8, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.49/1.06  tff(c_6, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.49/1.06  tff(c_30, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24, c_6])).
% 1.49/1.06  tff(c_38, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_30])).
% 1.49/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.06  
% 1.49/1.06  Inference rules
% 1.49/1.06  ----------------------
% 1.49/1.06  #Ref     : 0
% 1.49/1.06  #Sup     : 7
% 1.49/1.06  #Fact    : 0
% 1.49/1.06  #Define  : 0
% 1.49/1.06  #Split   : 0
% 1.49/1.06  #Chain   : 0
% 1.49/1.06  #Close   : 0
% 1.49/1.06  
% 1.49/1.06  Ordering : KBO
% 1.49/1.06  
% 1.49/1.06  Simplification rules
% 1.49/1.06  ----------------------
% 1.49/1.06  #Subsume      : 0
% 1.49/1.06  #Demod        : 1
% 1.49/1.06  #Tautology    : 3
% 1.49/1.06  #SimpNegUnit  : 0
% 1.49/1.06  #BackRed      : 0
% 1.49/1.06  
% 1.49/1.06  #Partial instantiations: 0
% 1.49/1.06  #Strategies tried      : 1
% 1.49/1.06  
% 1.49/1.06  Timing (in seconds)
% 1.49/1.06  ----------------------
% 1.49/1.06  Preprocessing        : 0.24
% 1.49/1.07  Parsing              : 0.13
% 1.49/1.07  CNF conversion       : 0.01
% 1.49/1.07  Main loop            : 0.08
% 1.49/1.07  Inferencing          : 0.04
% 1.49/1.07  Reduction            : 0.02
% 1.49/1.07  Demodulation         : 0.01
% 1.49/1.07  BG Simplification    : 0.01
% 1.49/1.07  Subsumption          : 0.01
% 1.49/1.07  Abstraction          : 0.00
% 1.49/1.07  MUC search           : 0.00
% 1.49/1.07  Cooper               : 0.00
% 1.49/1.07  Total                : 0.34
% 1.49/1.07  Index Insertion      : 0.00
% 1.49/1.07  Index Deletion       : 0.00
% 1.49/1.07  Index Matching       : 0.00
% 1.49/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
