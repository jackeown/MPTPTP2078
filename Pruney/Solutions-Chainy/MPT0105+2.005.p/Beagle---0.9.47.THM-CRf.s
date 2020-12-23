%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:48 EST 2020

% Result     : Theorem 7.00s
% Output     : CNFRefutation 7.00s
% Verified   : 
% Statistics : Number of formulae       :   36 (  50 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   27 (  41 expanded)
%              Number of equality atoms :   26 (  40 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_127,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k4_xboole_0(B_26,A_25)) = k5_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_230,plain,(
    ! [B_31,A_32] : k2_xboole_0(k4_xboole_0(B_31,A_32),k4_xboole_0(A_32,B_31)) = k5_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_236,plain,(
    ! [B_31,A_32] : k5_xboole_0(B_31,A_32) = k5_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_4])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,B_11)) = k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_75])).

tff(c_479,plain,(
    ! [A_43,B_44] : k2_xboole_0(k4_xboole_0(A_43,B_44),k3_xboole_0(A_43,B_44)) = k2_xboole_0(A_43,k4_xboole_0(A_43,B_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_491,plain,(
    ! [A_43,B_44] : k2_xboole_0(k3_xboole_0(A_43,B_44),k4_xboole_0(A_43,B_44)) = k2_xboole_0(A_43,k4_xboole_0(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_2])).

tff(c_527,plain,(
    ! [A_45,B_46] : k2_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_491])).

tff(c_545,plain,(
    ! [B_46] : k2_xboole_0(B_46,B_46) = B_46 ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_6])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7120,plain,(
    ! [A_156,B_157,C_158] : k2_xboole_0(k4_xboole_0(A_156,k2_xboole_0(B_157,C_158)),k4_xboole_0(C_158,k4_xboole_0(A_156,B_157))) = k5_xboole_0(k4_xboole_0(A_156,B_157),C_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_127])).

tff(c_7342,plain,(
    ! [A_156,B_46] : k2_xboole_0(k4_xboole_0(A_156,B_46),k4_xboole_0(B_46,k4_xboole_0(A_156,B_46))) = k5_xboole_0(k4_xboole_0(A_156,B_46),B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_7120])).

tff(c_7462,plain,(
    ! [B_46,A_156] : k5_xboole_0(B_46,k4_xboole_0(A_156,B_46)) = k2_xboole_0(B_46,A_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_6,c_2,c_6,c_7342])).

tff(c_14,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_7479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7462,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:44:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.00/2.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.00/2.64  
% 7.00/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.00/2.65  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 7.00/2.65  
% 7.00/2.65  %Foreground sorts:
% 7.00/2.65  
% 7.00/2.65  
% 7.00/2.65  %Background operators:
% 7.00/2.65  
% 7.00/2.65  
% 7.00/2.65  %Foreground operators:
% 7.00/2.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.00/2.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.00/2.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.00/2.65  tff('#skF_2', type, '#skF_2': $i).
% 7.00/2.65  tff('#skF_1', type, '#skF_1': $i).
% 7.00/2.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.00/2.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.00/2.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.00/2.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.00/2.65  
% 7.00/2.66  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.00/2.66  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 7.00/2.66  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.00/2.66  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 7.00/2.66  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.00/2.66  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.00/2.66  tff(f_40, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.00/2.66  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.00/2.66  tff(c_127, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k4_xboole_0(B_26, A_25))=k5_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.00/2.66  tff(c_230, plain, (![B_31, A_32]: (k2_xboole_0(k4_xboole_0(B_31, A_32), k4_xboole_0(A_32, B_31))=k5_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_2, c_127])).
% 7.00/2.66  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.00/2.66  tff(c_236, plain, (![B_31, A_32]: (k5_xboole_0(B_31, A_32)=k5_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_230, c_4])).
% 7.00/2.66  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.00/2.66  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.00/2.66  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.00/2.66  tff(c_75, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.00/2.66  tff(c_84, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, B_11))=k2_xboole_0(k4_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_75])).
% 7.00/2.66  tff(c_479, plain, (![A_43, B_44]: (k2_xboole_0(k4_xboole_0(A_43, B_44), k3_xboole_0(A_43, B_44))=k2_xboole_0(A_43, k4_xboole_0(A_43, B_44)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_84])).
% 7.00/2.66  tff(c_491, plain, (![A_43, B_44]: (k2_xboole_0(k3_xboole_0(A_43, B_44), k4_xboole_0(A_43, B_44))=k2_xboole_0(A_43, k4_xboole_0(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_479, c_2])).
% 7.00/2.66  tff(c_527, plain, (![A_45, B_46]: (k2_xboole_0(A_45, k4_xboole_0(A_45, B_46))=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_491])).
% 7.00/2.66  tff(c_545, plain, (![B_46]: (k2_xboole_0(B_46, B_46)=B_46)), inference(superposition, [status(thm), theory('equality')], [c_527, c_6])).
% 7.00/2.66  tff(c_8, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.00/2.66  tff(c_7120, plain, (![A_156, B_157, C_158]: (k2_xboole_0(k4_xboole_0(A_156, k2_xboole_0(B_157, C_158)), k4_xboole_0(C_158, k4_xboole_0(A_156, B_157)))=k5_xboole_0(k4_xboole_0(A_156, B_157), C_158))), inference(superposition, [status(thm), theory('equality')], [c_8, c_127])).
% 7.00/2.66  tff(c_7342, plain, (![A_156, B_46]: (k2_xboole_0(k4_xboole_0(A_156, B_46), k4_xboole_0(B_46, k4_xboole_0(A_156, B_46)))=k5_xboole_0(k4_xboole_0(A_156, B_46), B_46))), inference(superposition, [status(thm), theory('equality')], [c_545, c_7120])).
% 7.00/2.66  tff(c_7462, plain, (![B_46, A_156]: (k5_xboole_0(B_46, k4_xboole_0(A_156, B_46))=k2_xboole_0(B_46, A_156))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_6, c_2, c_6, c_7342])).
% 7.00/2.66  tff(c_14, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.00/2.66  tff(c_7479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7462, c_14])).
% 7.00/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.00/2.66  
% 7.00/2.66  Inference rules
% 7.00/2.66  ----------------------
% 7.00/2.66  #Ref     : 0
% 7.00/2.66  #Sup     : 1919
% 7.00/2.66  #Fact    : 0
% 7.00/2.66  #Define  : 0
% 7.00/2.66  #Split   : 0
% 7.00/2.66  #Chain   : 0
% 7.00/2.66  #Close   : 0
% 7.00/2.66  
% 7.00/2.66  Ordering : KBO
% 7.00/2.66  
% 7.00/2.66  Simplification rules
% 7.00/2.66  ----------------------
% 7.00/2.66  #Subsume      : 16
% 7.00/2.66  #Demod        : 2243
% 7.00/2.66  #Tautology    : 792
% 7.00/2.66  #SimpNegUnit  : 0
% 7.00/2.66  #BackRed      : 2
% 7.00/2.66  
% 7.00/2.66  #Partial instantiations: 0
% 7.00/2.66  #Strategies tried      : 1
% 7.00/2.66  
% 7.00/2.66  Timing (in seconds)
% 7.00/2.66  ----------------------
% 7.19/2.66  Preprocessing        : 0.25
% 7.19/2.66  Parsing              : 0.14
% 7.19/2.66  CNF conversion       : 0.01
% 7.19/2.66  Main loop            : 1.66
% 7.19/2.66  Inferencing          : 0.42
% 7.19/2.66  Reduction            : 0.87
% 7.19/2.66  Demodulation         : 0.77
% 7.19/2.66  BG Simplification    : 0.07
% 7.19/2.66  Subsumption          : 0.22
% 7.19/2.66  Abstraction          : 0.11
% 7.19/2.66  MUC search           : 0.00
% 7.19/2.66  Cooper               : 0.00
% 7.19/2.66  Total                : 1.94
% 7.19/2.66  Index Insertion      : 0.00
% 7.19/2.66  Index Deletion       : 0.00
% 7.19/2.66  Index Matching       : 0.00
% 7.19/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
