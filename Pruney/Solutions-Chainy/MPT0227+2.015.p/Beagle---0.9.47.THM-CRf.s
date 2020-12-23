%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:52 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_14,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_7,B_8] : k4_xboole_0(k1_tarski(A_7),k2_tarski(A_7,B_8)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2])).

tff(c_6,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:22:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.06  
% 1.51/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.07  %$ k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.51/1.07  
% 1.51/1.07  %Foreground sorts:
% 1.51/1.07  
% 1.51/1.07  
% 1.51/1.07  %Background operators:
% 1.51/1.07  
% 1.51/1.07  
% 1.51/1.07  %Foreground operators:
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.51/1.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.51/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.51/1.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.51/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.51/1.07  
% 1.51/1.08  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.51/1.08  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.51/1.08  tff(f_32, negated_conjecture, ~(![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.51/1.08  tff(c_14, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(B_8))=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.51/1.08  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.51/1.08  tff(c_20, plain, (![A_7, B_8]: (k4_xboole_0(k1_tarski(A_7), k2_tarski(A_7, B_8))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_2])).
% 1.51/1.08  tff(c_6, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.51/1.08  tff(c_28, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_6])).
% 1.51/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.08  
% 1.51/1.08  Inference rules
% 1.51/1.08  ----------------------
% 1.51/1.08  #Ref     : 0
% 1.51/1.08  #Sup     : 5
% 1.51/1.08  #Fact    : 0
% 1.51/1.08  #Define  : 0
% 1.51/1.08  #Split   : 0
% 1.51/1.08  #Chain   : 0
% 1.51/1.08  #Close   : 0
% 1.51/1.08  
% 1.51/1.08  Ordering : KBO
% 1.51/1.08  
% 1.51/1.08  Simplification rules
% 1.51/1.08  ----------------------
% 1.51/1.08  #Subsume      : 0
% 1.51/1.08  #Demod        : 1
% 1.51/1.08  #Tautology    : 4
% 1.51/1.08  #SimpNegUnit  : 0
% 1.51/1.08  #BackRed      : 1
% 1.51/1.08  
% 1.51/1.08  #Partial instantiations: 0
% 1.51/1.08  #Strategies tried      : 1
% 1.51/1.08  
% 1.51/1.08  Timing (in seconds)
% 1.51/1.08  ----------------------
% 1.51/1.08  Preprocessing        : 0.24
% 1.51/1.08  Parsing              : 0.13
% 1.51/1.08  CNF conversion       : 0.01
% 1.51/1.08  Main loop            : 0.06
% 1.51/1.08  Inferencing          : 0.03
% 1.51/1.08  Reduction            : 0.02
% 1.51/1.08  Demodulation         : 0.01
% 1.51/1.08  BG Simplification    : 0.01
% 1.51/1.08  Subsumption          : 0.00
% 1.51/1.08  Abstraction          : 0.00
% 1.51/1.08  MUC search           : 0.00
% 1.58/1.08  Cooper               : 0.00
% 1.58/1.08  Total                : 0.33
% 1.58/1.08  Index Insertion      : 0.00
% 1.58/1.08  Index Deletion       : 0.00
% 1.58/1.08  Index Matching       : 0.00
% 1.58/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
