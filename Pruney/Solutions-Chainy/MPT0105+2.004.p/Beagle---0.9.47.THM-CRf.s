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
% DateTime   : Thu Dec  3 09:44:48 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   26 (  38 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  30 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_11,B_12] : k4_xboole_0(k2_xboole_0(A_11,B_12),B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_75,plain,(
    ! [B_15,A_16] : k4_xboole_0(k2_xboole_0(B_15,A_16),B_15) = k4_xboole_0(A_16,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_91,plain,(
    ! [B_6,A_5] : k4_xboole_0(k4_xboole_0(B_6,A_5),A_5) = k4_xboole_0(k2_xboole_0(A_5,B_6),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_75])).

tff(c_106,plain,(
    ! [B_6,A_5] : k4_xboole_0(k4_xboole_0(B_6,A_5),A_5) = k4_xboole_0(B_6,A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_91])).

tff(c_110,plain,(
    ! [A_17,B_18] : k2_xboole_0(k4_xboole_0(A_17,B_18),k4_xboole_0(B_18,A_17)) = k5_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_303,plain,(
    ! [B_27,A_28] : k2_xboole_0(k4_xboole_0(B_27,A_28),k4_xboole_0(A_28,B_27)) = k5_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_110])).

tff(c_333,plain,(
    ! [B_6,A_5] : k2_xboole_0(k4_xboole_0(B_6,A_5),k4_xboole_0(A_5,k4_xboole_0(B_6,A_5))) = k5_xboole_0(A_5,k4_xboole_0(B_6,A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_303])).

tff(c_364,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2,c_6,c_333])).

tff(c_10,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  
% 2.06/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  %$ k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 2.06/1.22  
% 2.06/1.22  %Foreground sorts:
% 2.06/1.22  
% 2.06/1.22  
% 2.06/1.22  %Background operators:
% 2.06/1.22  
% 2.06/1.22  
% 2.06/1.22  %Foreground operators:
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.06/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.22  
% 2.06/1.23  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.06/1.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.06/1.23  tff(f_33, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.06/1.23  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.06/1.23  tff(f_36, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.06/1.23  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.23  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.23  tff(c_44, plain, (![A_11, B_12]: (k4_xboole_0(k2_xboole_0(A_11, B_12), B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.23  tff(c_53, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_44])).
% 2.06/1.23  tff(c_75, plain, (![B_15, A_16]: (k4_xboole_0(k2_xboole_0(B_15, A_16), B_15)=k4_xboole_0(A_16, B_15))), inference(superposition, [status(thm), theory('equality')], [c_2, c_44])).
% 2.06/1.23  tff(c_91, plain, (![B_6, A_5]: (k4_xboole_0(k4_xboole_0(B_6, A_5), A_5)=k4_xboole_0(k2_xboole_0(A_5, B_6), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_75])).
% 2.06/1.23  tff(c_106, plain, (![B_6, A_5]: (k4_xboole_0(k4_xboole_0(B_6, A_5), A_5)=k4_xboole_0(B_6, A_5))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_91])).
% 2.06/1.23  tff(c_110, plain, (![A_17, B_18]: (k2_xboole_0(k4_xboole_0(A_17, B_18), k4_xboole_0(B_18, A_17))=k5_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.23  tff(c_303, plain, (![B_27, A_28]: (k2_xboole_0(k4_xboole_0(B_27, A_28), k4_xboole_0(A_28, B_27))=k5_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_2, c_110])).
% 2.06/1.23  tff(c_333, plain, (![B_6, A_5]: (k2_xboole_0(k4_xboole_0(B_6, A_5), k4_xboole_0(A_5, k4_xboole_0(B_6, A_5)))=k5_xboole_0(A_5, k4_xboole_0(B_6, A_5)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_303])).
% 2.06/1.23  tff(c_364, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2, c_6, c_333])).
% 2.06/1.23  tff(c_10, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.06/1.23  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_364, c_10])).
% 2.06/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  Inference rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Ref     : 0
% 2.06/1.23  #Sup     : 104
% 2.06/1.23  #Fact    : 0
% 2.06/1.23  #Define  : 0
% 2.06/1.23  #Split   : 0
% 2.06/1.23  #Chain   : 0
% 2.06/1.23  #Close   : 0
% 2.06/1.23  
% 2.06/1.23  Ordering : KBO
% 2.06/1.23  
% 2.06/1.23  Simplification rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Subsume      : 3
% 2.06/1.23  #Demod        : 63
% 2.06/1.23  #Tautology    : 62
% 2.06/1.23  #SimpNegUnit  : 0
% 2.06/1.23  #BackRed      : 1
% 2.06/1.23  
% 2.06/1.23  #Partial instantiations: 0
% 2.06/1.23  #Strategies tried      : 1
% 2.06/1.23  
% 2.06/1.23  Timing (in seconds)
% 2.06/1.23  ----------------------
% 2.06/1.23  Preprocessing        : 0.25
% 2.13/1.23  Parsing              : 0.14
% 2.13/1.23  CNF conversion       : 0.01
% 2.13/1.23  Main loop            : 0.23
% 2.13/1.23  Inferencing          : 0.07
% 2.13/1.23  Reduction            : 0.10
% 2.13/1.23  Demodulation         : 0.09
% 2.13/1.23  BG Simplification    : 0.01
% 2.13/1.23  Subsumption          : 0.03
% 2.13/1.23  Abstraction          : 0.01
% 2.13/1.23  MUC search           : 0.00
% 2.13/1.23  Cooper               : 0.00
% 2.13/1.23  Total                : 0.50
% 2.13/1.23  Index Insertion      : 0.00
% 2.13/1.23  Index Deletion       : 0.00
% 2.13/1.24  Index Matching       : 0.00
% 2.13/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
