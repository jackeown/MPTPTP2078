%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:51 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_10,B_11] : k3_xboole_0(k1_tarski(A_10),k2_tarski(A_10,B_11)) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_10,B_11] : k5_xboole_0(k1_tarski(A_10),k1_tarski(A_10)) = k4_xboole_0(k1_tarski(A_10),k2_tarski(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_52])).

tff(c_64,plain,(
    ! [A_10,B_11] : k4_xboole_0(k1_tarski(A_10),k2_tarski(A_10,B_11)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_61])).

tff(c_14,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.08  
% 1.62/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.09  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.62/1.09  
% 1.62/1.09  %Foreground sorts:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Background operators:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Foreground operators:
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.62/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.62/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.62/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.62/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.09  
% 1.62/1.09  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.62/1.09  tff(f_37, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 1.62/1.09  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.62/1.09  tff(f_40, negated_conjecture, ~(![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.62/1.09  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.09  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(k1_tarski(A_10), k2_tarski(A_10, B_11))=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.09  tff(c_52, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.09  tff(c_61, plain, (![A_10, B_11]: (k5_xboole_0(k1_tarski(A_10), k1_tarski(A_10))=k4_xboole_0(k1_tarski(A_10), k2_tarski(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_52])).
% 1.62/1.09  tff(c_64, plain, (![A_10, B_11]: (k4_xboole_0(k1_tarski(A_10), k2_tarski(A_10, B_11))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_61])).
% 1.62/1.09  tff(c_14, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.09  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_14])).
% 1.62/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  Inference rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Ref     : 0
% 1.62/1.09  #Sup     : 17
% 1.62/1.09  #Fact    : 0
% 1.62/1.09  #Define  : 0
% 1.62/1.09  #Split   : 0
% 1.62/1.09  #Chain   : 0
% 1.62/1.09  #Close   : 0
% 1.62/1.09  
% 1.62/1.09  Ordering : KBO
% 1.62/1.09  
% 1.62/1.09  Simplification rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Subsume      : 0
% 1.62/1.09  #Demod        : 3
% 1.62/1.09  #Tautology    : 14
% 1.62/1.09  #SimpNegUnit  : 0
% 1.62/1.09  #BackRed      : 1
% 1.62/1.09  
% 1.62/1.09  #Partial instantiations: 0
% 1.62/1.09  #Strategies tried      : 1
% 1.62/1.09  
% 1.62/1.09  Timing (in seconds)
% 1.62/1.09  ----------------------
% 1.62/1.10  Preprocessing        : 0.26
% 1.62/1.10  Parsing              : 0.14
% 1.62/1.10  CNF conversion       : 0.01
% 1.62/1.10  Main loop            : 0.08
% 1.62/1.10  Inferencing          : 0.04
% 1.62/1.10  Reduction            : 0.03
% 1.62/1.10  Demodulation         : 0.02
% 1.62/1.10  BG Simplification    : 0.01
% 1.62/1.10  Subsumption          : 0.01
% 1.62/1.10  Abstraction          : 0.01
% 1.62/1.10  MUC search           : 0.00
% 1.62/1.10  Cooper               : 0.00
% 1.62/1.10  Total                : 0.37
% 1.62/1.10  Index Insertion      : 0.00
% 1.62/1.10  Index Deletion       : 0.00
% 1.62/1.10  Index Matching       : 0.00
% 1.62/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
