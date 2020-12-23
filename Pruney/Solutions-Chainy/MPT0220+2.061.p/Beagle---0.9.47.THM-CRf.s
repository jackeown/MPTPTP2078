%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:12 EST 2020

% Result     : Theorem 1.42s
% Output     : CNFRefutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :    9 (  11 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k1_tarski(B_4)) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_31,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k2_tarski(A_3,B_4)) = k2_xboole_0(k1_tarski(A_3),k1_tarski(B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_16])).

tff(c_36,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),k2_tarski(A_3,B_4)) = k2_tarski(A_3,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_6,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:33:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.42/1.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.42/1.02  
% 1.42/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.42/1.02  %$ k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.42/1.02  
% 1.42/1.02  %Foreground sorts:
% 1.42/1.02  
% 1.42/1.02  
% 1.42/1.02  %Background operators:
% 1.42/1.02  
% 1.42/1.02  
% 1.42/1.02  %Foreground operators:
% 1.42/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.42/1.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.42/1.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.42/1.02  tff('#skF_2', type, '#skF_2': $i).
% 1.42/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.42/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.42/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.42/1.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.42/1.02  
% 1.42/1.03  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.42/1.03  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 1.42/1.03  tff(f_32, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 1.42/1.03  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k1_tarski(B_4))=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.42/1.03  tff(c_16, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.42/1.03  tff(c_31, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k2_tarski(A_3, B_4))=k2_xboole_0(k1_tarski(A_3), k1_tarski(B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_16])).
% 1.42/1.03  tff(c_36, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), k2_tarski(A_3, B_4))=k2_tarski(A_3, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_31])).
% 1.42/1.03  tff(c_6, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.42/1.03  tff(c_39, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_6])).
% 1.42/1.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.42/1.03  
% 1.42/1.03  Inference rules
% 1.42/1.03  ----------------------
% 1.42/1.03  #Ref     : 0
% 1.42/1.03  #Sup     : 7
% 1.42/1.03  #Fact    : 0
% 1.42/1.03  #Define  : 0
% 1.42/1.03  #Split   : 0
% 1.42/1.03  #Chain   : 0
% 1.42/1.03  #Close   : 0
% 1.42/1.03  
% 1.42/1.03  Ordering : KBO
% 1.42/1.03  
% 1.42/1.03  Simplification rules
% 1.42/1.03  ----------------------
% 1.42/1.03  #Subsume      : 0
% 1.42/1.03  #Demod        : 6
% 1.42/1.03  #Tautology    : 6
% 1.42/1.03  #SimpNegUnit  : 0
% 1.42/1.03  #BackRed      : 1
% 1.42/1.03  
% 1.42/1.03  #Partial instantiations: 0
% 1.42/1.03  #Strategies tried      : 1
% 1.42/1.03  
% 1.42/1.03  Timing (in seconds)
% 1.42/1.03  ----------------------
% 1.42/1.03  Preprocessing        : 0.23
% 1.42/1.03  Parsing              : 0.13
% 1.42/1.03  CNF conversion       : 0.01
% 1.42/1.03  Main loop            : 0.07
% 1.42/1.03  Inferencing          : 0.03
% 1.42/1.03  Reduction            : 0.02
% 1.42/1.03  Demodulation         : 0.02
% 1.42/1.03  BG Simplification    : 0.01
% 1.42/1.03  Subsumption          : 0.01
% 1.42/1.03  Abstraction          : 0.00
% 1.42/1.03  MUC search           : 0.00
% 1.42/1.03  Cooper               : 0.00
% 1.42/1.03  Total                : 0.32
% 1.42/1.04  Index Insertion      : 0.00
% 1.42/1.04  Index Deletion       : 0.00
% 1.42/1.04  Index Matching       : 0.00
% 1.42/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
