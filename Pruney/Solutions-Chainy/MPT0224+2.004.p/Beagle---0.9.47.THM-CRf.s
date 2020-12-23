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
% DateTime   : Thu Dec  3 09:48:29 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(c_197,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),k1_tarski(B_26)) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,(
    ! [A_25,B_26] : k3_xboole_0(k1_tarski(A_25),k2_tarski(A_25,B_26)) = k1_tarski(A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_6])).

tff(c_14,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.15  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.79/1.15  
% 1.79/1.15  %Foreground sorts:
% 1.79/1.15  
% 1.79/1.15  
% 1.79/1.15  %Background operators:
% 1.79/1.15  
% 1.79/1.15  
% 1.79/1.15  %Foreground operators:
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.79/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.79/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.15  
% 1.79/1.16  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.79/1.16  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.79/1.16  tff(f_40, negated_conjecture, ~(![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 1.79/1.16  tff(c_197, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(B_26))=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.79/1.16  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.16  tff(c_203, plain, (![A_25, B_26]: (k3_xboole_0(k1_tarski(A_25), k2_tarski(A_25, B_26))=k1_tarski(A_25))), inference(superposition, [status(thm), theory('equality')], [c_197, c_6])).
% 1.79/1.16  tff(c_14, plain, (k3_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.16  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_14])).
% 1.79/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.16  
% 1.79/1.16  Inference rules
% 1.79/1.16  ----------------------
% 1.79/1.16  #Ref     : 0
% 1.79/1.16  #Sup     : 65
% 1.79/1.16  #Fact    : 0
% 1.79/1.16  #Define  : 0
% 1.79/1.16  #Split   : 0
% 1.79/1.16  #Chain   : 0
% 1.79/1.16  #Close   : 0
% 1.79/1.16  
% 1.79/1.16  Ordering : KBO
% 1.79/1.16  
% 1.79/1.16  Simplification rules
% 1.79/1.16  ----------------------
% 1.79/1.16  #Subsume      : 16
% 1.79/1.16  #Demod        : 15
% 1.79/1.16  #Tautology    : 40
% 1.79/1.16  #SimpNegUnit  : 0
% 1.79/1.16  #BackRed      : 1
% 1.79/1.16  
% 1.79/1.16  #Partial instantiations: 0
% 1.79/1.16  #Strategies tried      : 1
% 1.79/1.16  
% 1.79/1.16  Timing (in seconds)
% 1.79/1.16  ----------------------
% 1.79/1.16  Preprocessing        : 0.27
% 1.79/1.16  Parsing              : 0.14
% 1.79/1.16  CNF conversion       : 0.01
% 1.79/1.16  Main loop            : 0.13
% 1.79/1.16  Inferencing          : 0.05
% 1.79/1.16  Reduction            : 0.05
% 1.79/1.16  Demodulation         : 0.04
% 1.79/1.16  BG Simplification    : 0.01
% 1.79/1.16  Subsumption          : 0.02
% 1.79/1.16  Abstraction          : 0.01
% 1.79/1.16  MUC search           : 0.00
% 1.79/1.16  Cooper               : 0.00
% 1.79/1.16  Total                : 0.42
% 1.79/1.16  Index Insertion      : 0.00
% 1.79/1.16  Index Deletion       : 0.00
% 1.79/1.16  Index Matching       : 0.00
% 1.79/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
