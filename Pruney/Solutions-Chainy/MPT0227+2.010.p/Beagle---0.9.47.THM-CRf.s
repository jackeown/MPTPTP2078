%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:51 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k1_tarski(A_6),k2_tarski(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_27,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [A_6,B_7] : k4_xboole_0(k1_tarski(A_6),k2_tarski(A_6,B_7)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_27])).

tff(c_12,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.17  
% 1.72/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.17  %$ r1_tarski > k2_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.72/1.17  
% 1.72/1.17  %Foreground sorts:
% 1.72/1.17  
% 1.72/1.17  
% 1.72/1.17  %Background operators:
% 1.72/1.17  
% 1.72/1.17  
% 1.72/1.17  %Foreground operators:
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.17  
% 1.72/1.18  tff(f_35, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.72/1.18  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.72/1.18  tff(f_38, negated_conjecture, ~(![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.72/1.18  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), k2_tarski(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.18  tff(c_27, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.72/1.18  tff(c_35, plain, (![A_6, B_7]: (k4_xboole_0(k1_tarski(A_6), k2_tarski(A_6, B_7))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_27])).
% 1.72/1.18  tff(c_12, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.72/1.18  tff(c_50, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35, c_12])).
% 1.72/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.18  
% 1.72/1.18  Inference rules
% 1.72/1.18  ----------------------
% 1.72/1.18  #Ref     : 0
% 1.72/1.18  #Sup     : 8
% 1.72/1.18  #Fact    : 0
% 1.72/1.18  #Define  : 0
% 1.72/1.18  #Split   : 0
% 1.72/1.18  #Chain   : 0
% 1.72/1.18  #Close   : 0
% 1.72/1.18  
% 1.72/1.18  Ordering : KBO
% 1.72/1.18  
% 1.72/1.18  Simplification rules
% 1.72/1.18  ----------------------
% 1.72/1.18  #Subsume      : 0
% 1.72/1.18  #Demod        : 1
% 1.72/1.18  #Tautology    : 5
% 1.72/1.18  #SimpNegUnit  : 0
% 1.72/1.18  #BackRed      : 1
% 1.72/1.18  
% 1.72/1.18  #Partial instantiations: 0
% 1.72/1.18  #Strategies tried      : 1
% 1.72/1.18  
% 1.72/1.18  Timing (in seconds)
% 1.72/1.18  ----------------------
% 1.72/1.18  Preprocessing        : 0.28
% 1.72/1.18  Parsing              : 0.15
% 1.72/1.18  CNF conversion       : 0.02
% 1.72/1.18  Main loop            : 0.07
% 1.72/1.18  Inferencing          : 0.03
% 1.72/1.18  Reduction            : 0.02
% 1.72/1.18  Demodulation         : 0.02
% 1.72/1.18  BG Simplification    : 0.01
% 1.72/1.18  Subsumption          : 0.01
% 1.72/1.18  Abstraction          : 0.01
% 1.72/1.18  MUC search           : 0.00
% 1.72/1.18  Cooper               : 0.00
% 1.72/1.18  Total                : 0.37
% 1.72/1.18  Index Insertion      : 0.00
% 1.72/1.18  Index Deletion       : 0.00
% 1.72/1.18  Index Matching       : 0.00
% 1.72/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
