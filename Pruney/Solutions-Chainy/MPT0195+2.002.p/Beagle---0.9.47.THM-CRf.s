%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:00 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   12 (  16 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_enumset1)).

tff(c_428,plain,(
    ! [B_107,D_108,A_109,C_110] : k2_enumset1(B_107,D_108,A_109,C_110) = k2_enumset1(A_109,B_107,C_110,D_108) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_14,D_16,C_15,A_13] : k2_enumset1(B_14,D_16,C_15,A_13) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_482,plain,(
    ! [B_107,D_108,C_110,A_109] : k2_enumset1(B_107,D_108,C_110,A_109) = k2_enumset1(B_107,D_108,A_109,C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_10])).

tff(c_6,plain,(
    ! [A_5,C_7,D_8,B_6] : k2_enumset1(A_5,C_7,D_8,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_1','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_32])).

tff(c_34,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_4169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:12:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/2.07  
% 5.22/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/2.07  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.22/2.07  
% 5.22/2.07  %Foreground sorts:
% 5.22/2.07  
% 5.22/2.07  
% 5.22/2.07  %Background operators:
% 5.22/2.07  
% 5.22/2.07  
% 5.22/2.07  %Foreground operators:
% 5.22/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.22/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.22/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.22/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.22/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.22/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.22/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.22/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.22/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.22/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.22/2.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.22/2.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.22/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.22/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.22/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.22/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.22/2.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.22/2.07  
% 5.22/2.08  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_enumset1)).
% 5.22/2.08  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 5.22/2.08  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_enumset1)).
% 5.22/2.08  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_enumset1)).
% 5.22/2.08  tff(c_428, plain, (![B_107, D_108, A_109, C_110]: (k2_enumset1(B_107, D_108, A_109, C_110)=k2_enumset1(A_109, B_107, C_110, D_108))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.22/2.08  tff(c_10, plain, (![B_14, D_16, C_15, A_13]: (k2_enumset1(B_14, D_16, C_15, A_13)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.22/2.08  tff(c_482, plain, (![B_107, D_108, C_110, A_109]: (k2_enumset1(B_107, D_108, C_110, A_109)=k2_enumset1(B_107, D_108, A_109, C_110))), inference(superposition, [status(thm), theory('equality')], [c_428, c_10])).
% 5.22/2.08  tff(c_6, plain, (![A_5, C_7, D_8, B_6]: (k2_enumset1(A_5, C_7, D_8, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.22/2.08  tff(c_32, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_1', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.22/2.08  tff(c_33, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_32])).
% 5.22/2.08  tff(c_34, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_33])).
% 5.22/2.08  tff(c_4169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_482, c_34])).
% 5.22/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/2.08  
% 5.22/2.08  Inference rules
% 5.22/2.08  ----------------------
% 5.22/2.08  #Ref     : 0
% 5.22/2.08  #Sup     : 1067
% 5.22/2.08  #Fact    : 0
% 5.22/2.08  #Define  : 0
% 5.22/2.08  #Split   : 0
% 5.22/2.08  #Chain   : 0
% 5.22/2.08  #Close   : 0
% 5.22/2.08  
% 5.22/2.08  Ordering : KBO
% 5.22/2.08  
% 5.22/2.08  Simplification rules
% 5.22/2.08  ----------------------
% 5.22/2.08  #Subsume      : 240
% 5.22/2.08  #Demod        : 411
% 5.22/2.08  #Tautology    : 565
% 5.22/2.08  #SimpNegUnit  : 0
% 5.22/2.08  #BackRed      : 1
% 5.22/2.08  
% 5.22/2.08  #Partial instantiations: 0
% 5.22/2.08  #Strategies tried      : 1
% 5.22/2.08  
% 5.22/2.08  Timing (in seconds)
% 5.22/2.08  ----------------------
% 5.22/2.08  Preprocessing        : 0.35
% 5.22/2.08  Parsing              : 0.16
% 5.22/2.08  CNF conversion       : 0.02
% 5.22/2.08  Main loop            : 0.95
% 5.22/2.08  Inferencing          : 0.30
% 5.22/2.08  Reduction            : 0.45
% 5.22/2.08  Demodulation         : 0.40
% 5.22/2.08  BG Simplification    : 0.04
% 5.22/2.08  Subsumption          : 0.12
% 5.22/2.08  Abstraction          : 0.06
% 5.22/2.08  MUC search           : 0.00
% 5.22/2.08  Cooper               : 0.00
% 5.22/2.08  Total                : 1.33
% 5.22/2.08  Index Insertion      : 0.00
% 5.22/2.08  Index Deletion       : 0.00
% 5.22/2.08  Index Matching       : 0.00
% 5.22/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
