%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:37 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   20 (  27 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   12 (  19 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_34,negated_conjecture,(
    ~ ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_25,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_18])).

tff(c_35,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),k4_xboole_0(B_11,A_10)) = k5_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_47,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_3,A_3)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_35])).

tff(c_59,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_25,c_47])).

tff(c_8,plain,(
    k5_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.08  
% 1.60/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.09  %$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.60/1.09  
% 1.60/1.09  %Foreground sorts:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Background operators:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Foreground operators:
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.60/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.60/1.09  
% 1.60/1.09  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.60/1.09  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.60/1.09  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.60/1.09  tff(f_34, negated_conjecture, ~(![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.60/1.09  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.09  tff(c_18, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.09  tff(c_25, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_18])).
% 1.60/1.09  tff(c_35, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k4_xboole_0(B_11, A_10))=k5_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.09  tff(c_47, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_3, A_3))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_25, c_35])).
% 1.60/1.09  tff(c_59, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_25, c_47])).
% 1.60/1.09  tff(c_8, plain, (k5_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.60/1.09  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_8])).
% 1.60/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.09  
% 1.60/1.09  Inference rules
% 1.60/1.09  ----------------------
% 1.60/1.09  #Ref     : 0
% 1.60/1.09  #Sup     : 22
% 1.60/1.09  #Fact    : 0
% 1.60/1.09  #Define  : 0
% 1.60/1.09  #Split   : 0
% 1.60/1.09  #Chain   : 0
% 1.60/1.09  #Close   : 0
% 1.60/1.09  
% 1.60/1.09  Ordering : KBO
% 1.60/1.09  
% 1.60/1.09  Simplification rules
% 1.60/1.09  ----------------------
% 1.60/1.09  #Subsume      : 0
% 1.60/1.09  #Demod        : 7
% 1.60/1.09  #Tautology    : 10
% 1.60/1.09  #SimpNegUnit  : 0
% 1.60/1.09  #BackRed      : 1
% 1.60/1.09  
% 1.60/1.09  #Partial instantiations: 0
% 1.60/1.09  #Strategies tried      : 1
% 1.60/1.09  
% 1.60/1.09  Timing (in seconds)
% 1.60/1.09  ----------------------
% 1.60/1.10  Preprocessing        : 0.23
% 1.60/1.10  Parsing              : 0.13
% 1.60/1.10  CNF conversion       : 0.01
% 1.60/1.10  Main loop            : 0.09
% 1.60/1.10  Inferencing          : 0.04
% 1.60/1.10  Reduction            : 0.04
% 1.60/1.10  Demodulation         : 0.03
% 1.60/1.10  BG Simplification    : 0.01
% 1.60/1.10  Subsumption          : 0.01
% 1.60/1.10  Abstraction          : 0.01
% 1.60/1.10  MUC search           : 0.00
% 1.60/1.10  Cooper               : 0.00
% 1.60/1.10  Total                : 0.35
% 1.60/1.10  Index Insertion      : 0.00
% 1.60/1.10  Index Deletion       : 0.00
% 1.60/1.10  Index Matching       : 0.00
% 1.60/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
