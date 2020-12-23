%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:32 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   27 (  63 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   21 (  62 expanded)
%              Number of equality atoms :   20 (  61 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(A,B) = k1_xboole_0
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [B_11,A_12] : k2_xboole_0(B_11,A_12) = k2_xboole_0(A_12,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_6])).

tff(c_12,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k2_xboole_0(A_13,B_14),C_15) = k2_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_149,plain,(
    ! [C_15] : k2_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_15)) = k2_xboole_0(k1_xboole_0,C_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_92])).

tff(c_210,plain,(
    ! [C_17] : k2_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_17)) = C_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_149])).

tff(c_235,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_210])).

tff(c_241,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_12])).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_252,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_10])).

tff(c_251,plain,(
    ! [A_5] : k2_xboole_0(A_5,'#skF_2') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_6])).

tff(c_296,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_235])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.21  
% 1.86/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  %$ k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.21  
% 1.97/1.21  %Foreground sorts:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Background operators:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Foreground operators:
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.21  
% 1.97/1.22  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.97/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.97/1.22  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.97/1.22  tff(f_38, negated_conjecture, ~(![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.97/1.22  tff(f_33, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.97/1.22  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.22  tff(c_45, plain, (![B_11, A_12]: (k2_xboole_0(B_11, A_12)=k2_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.22  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.22  tff(c_61, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, A_12)=A_12)), inference(superposition, [status(thm), theory('equality')], [c_45, c_6])).
% 1.97/1.22  tff(c_12, plain, (k2_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.97/1.22  tff(c_92, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k2_xboole_0(A_13, B_14), C_15)=k2_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.22  tff(c_149, plain, (![C_15]: (k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_15))=k2_xboole_0(k1_xboole_0, C_15))), inference(superposition, [status(thm), theory('equality')], [c_12, c_92])).
% 1.97/1.22  tff(c_210, plain, (![C_17]: (k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_17))=C_17)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_149])).
% 1.97/1.22  tff(c_235, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4, c_210])).
% 1.97/1.22  tff(c_241, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_235, c_12])).
% 1.97/1.22  tff(c_10, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.97/1.22  tff(c_252, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_10])).
% 1.97/1.22  tff(c_251, plain, (![A_5]: (k2_xboole_0(A_5, '#skF_2')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_241, c_6])).
% 1.97/1.22  tff(c_296, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_251, c_235])).
% 1.97/1.22  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_296])).
% 1.97/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  Inference rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Ref     : 0
% 1.97/1.22  #Sup     : 69
% 1.97/1.22  #Fact    : 0
% 1.97/1.22  #Define  : 0
% 1.97/1.22  #Split   : 0
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 0
% 1.97/1.22  #Demod        : 30
% 1.97/1.22  #Tautology    : 50
% 1.97/1.22  #SimpNegUnit  : 1
% 1.97/1.22  #BackRed      : 6
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.23  Preprocessing        : 0.28
% 1.97/1.23  Parsing              : 0.15
% 1.97/1.23  CNF conversion       : 0.02
% 1.97/1.23  Main loop            : 0.17
% 1.97/1.23  Inferencing          : 0.06
% 1.97/1.23  Reduction            : 0.07
% 1.97/1.23  Demodulation         : 0.06
% 1.97/1.23  BG Simplification    : 0.01
% 1.97/1.23  Subsumption          : 0.02
% 1.97/1.23  Abstraction          : 0.01
% 1.97/1.23  MUC search           : 0.00
% 1.97/1.23  Cooper               : 0.00
% 1.97/1.23  Total                : 0.47
% 1.97/1.23  Index Insertion      : 0.00
% 1.97/1.23  Index Deletion       : 0.00
% 1.97/1.23  Index Matching       : 0.00
% 1.97/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
