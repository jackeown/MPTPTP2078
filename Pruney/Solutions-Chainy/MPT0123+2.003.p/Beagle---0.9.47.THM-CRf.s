%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:35 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   33 (  47 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   24 (  38 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k3_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k3_xboole_0(k3_xboole_0(A_1,B_2),C_3) = k3_xboole_0(A_1,k3_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_29,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),k3_xboole_0(A_17,k4_xboole_0(B_18,C_19))) = k3_xboole_0(k3_xboole_0(A_17,B_18),C_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_6])).

tff(c_849,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),k3_xboole_0(A_17,k4_xboole_0(B_18,C_19))) = k3_xboole_0(A_17,k3_xboole_0(B_18,C_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_35])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k4_xboole_0(A_12,B_13),k3_xboole_0(A_12,C_14)) = k4_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k3_xboole_0(A_9,B_10),C_11) = k3_xboole_0(A_9,k4_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k4_xboole_0(A_20,B_21),C_22) = k4_xboole_0(A_20,k2_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_7,B_8,C_22] : k4_xboole_0(A_7,k2_xboole_0(k4_xboole_0(A_7,B_8),C_22)) = k4_xboole_0(k3_xboole_0(A_7,B_8),C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_51])).

tff(c_180,plain,(
    ! [A_31,B_32,C_33] : k4_xboole_0(A_31,k2_xboole_0(k4_xboole_0(A_31,B_32),C_33)) = k3_xboole_0(A_31,k4_xboole_0(B_32,C_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_212,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(A_12,k4_xboole_0(A_12,k4_xboole_0(B_13,C_14))) = k3_xboole_0(A_12,k4_xboole_0(B_13,k3_xboole_0(A_12,C_14))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_180])).

tff(c_238,plain,(
    ! [A_12,B_13,C_14] : k3_xboole_0(A_12,k4_xboole_0(B_13,k3_xboole_0(A_12,C_14))) = k3_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_212])).

tff(c_850,plain,(
    ! [A_56,B_57,C_58] : k4_xboole_0(k3_xboole_0(A_56,B_57),k3_xboole_0(A_56,k4_xboole_0(B_57,C_58))) = k3_xboole_0(A_56,k3_xboole_0(B_57,C_58)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_35])).

tff(c_910,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k3_xboole_0(A_12,B_13),k3_xboole_0(A_12,k4_xboole_0(B_13,C_14))) = k3_xboole_0(A_12,k3_xboole_0(B_13,k3_xboole_0(A_12,C_14))) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_850])).

tff(c_956,plain,(
    ! [A_12,B_13,C_14] : k3_xboole_0(A_12,k3_xboole_0(B_13,k3_xboole_0(A_12,C_14))) = k3_xboole_0(A_12,k3_xboole_0(B_13,C_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_910])).

tff(c_12,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3'))) != k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.52  
% 3.18/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.52  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.18/1.52  
% 3.18/1.52  %Foreground sorts:
% 3.18/1.52  
% 3.18/1.52  
% 3.18/1.52  %Background operators:
% 3.18/1.52  
% 3.18/1.52  
% 3.18/1.52  %Foreground operators:
% 3.18/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.52  
% 3.18/1.53  tff(f_27, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.18/1.53  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.18/1.53  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.18/1.53  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.18/1.53  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.18/1.53  tff(f_38, negated_conjecture, ~(![A, B, C]: (k3_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_xboole_1)).
% 3.18/1.53  tff(c_2, plain, (![A_1, B_2, C_3]: (k3_xboole_0(k3_xboole_0(A_1, B_2), C_3)=k3_xboole_0(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.18/1.53  tff(c_29, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), C_19)=k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.53  tff(c_6, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.53  tff(c_35, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))=k3_xboole_0(k3_xboole_0(A_17, B_18), C_19))), inference(superposition, [status(thm), theory('equality')], [c_29, c_6])).
% 3.18/1.53  tff(c_849, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))=k3_xboole_0(A_17, k3_xboole_0(B_18, C_19)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_35])).
% 3.18/1.53  tff(c_10, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k4_xboole_0(A_12, B_13), k3_xboole_0(A_12, C_14))=k4_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.18/1.53  tff(c_8, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k3_xboole_0(A_9, B_10), C_11)=k3_xboole_0(A_9, k4_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.53  tff(c_51, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k4_xboole_0(A_20, B_21), C_22)=k4_xboole_0(A_20, k2_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.53  tff(c_76, plain, (![A_7, B_8, C_22]: (k4_xboole_0(A_7, k2_xboole_0(k4_xboole_0(A_7, B_8), C_22))=k4_xboole_0(k3_xboole_0(A_7, B_8), C_22))), inference(superposition, [status(thm), theory('equality')], [c_6, c_51])).
% 3.18/1.53  tff(c_180, plain, (![A_31, B_32, C_33]: (k4_xboole_0(A_31, k2_xboole_0(k4_xboole_0(A_31, B_32), C_33))=k3_xboole_0(A_31, k4_xboole_0(B_32, C_33)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_76])).
% 3.18/1.53  tff(c_212, plain, (![A_12, B_13, C_14]: (k4_xboole_0(A_12, k4_xboole_0(A_12, k4_xboole_0(B_13, C_14)))=k3_xboole_0(A_12, k4_xboole_0(B_13, k3_xboole_0(A_12, C_14))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_180])).
% 3.18/1.53  tff(c_238, plain, (![A_12, B_13, C_14]: (k3_xboole_0(A_12, k4_xboole_0(B_13, k3_xboole_0(A_12, C_14)))=k3_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_212])).
% 3.18/1.53  tff(c_850, plain, (![A_56, B_57, C_58]: (k4_xboole_0(k3_xboole_0(A_56, B_57), k3_xboole_0(A_56, k4_xboole_0(B_57, C_58)))=k3_xboole_0(A_56, k3_xboole_0(B_57, C_58)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_35])).
% 3.18/1.53  tff(c_910, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k3_xboole_0(A_12, B_13), k3_xboole_0(A_12, k4_xboole_0(B_13, C_14)))=k3_xboole_0(A_12, k3_xboole_0(B_13, k3_xboole_0(A_12, C_14))))), inference(superposition, [status(thm), theory('equality')], [c_238, c_850])).
% 3.18/1.53  tff(c_956, plain, (![A_12, B_13, C_14]: (k3_xboole_0(A_12, k3_xboole_0(B_13, k3_xboole_0(A_12, C_14)))=k3_xboole_0(A_12, k3_xboole_0(B_13, C_14)))), inference(demodulation, [status(thm), theory('equality')], [c_849, c_910])).
% 3.18/1.53  tff(c_12, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.53  tff(c_13, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_3')))!=k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 3.18/1.53  tff(c_964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_956, c_13])).
% 3.18/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.53  
% 3.18/1.53  Inference rules
% 3.18/1.53  ----------------------
% 3.18/1.53  #Ref     : 0
% 3.18/1.53  #Sup     : 230
% 3.18/1.53  #Fact    : 0
% 3.18/1.53  #Define  : 0
% 3.18/1.53  #Split   : 0
% 3.18/1.53  #Chain   : 0
% 3.18/1.53  #Close   : 0
% 3.18/1.53  
% 3.18/1.53  Ordering : KBO
% 3.18/1.53  
% 3.18/1.53  Simplification rules
% 3.18/1.53  ----------------------
% 3.18/1.53  #Subsume      : 0
% 3.18/1.53  #Demod        : 405
% 3.18/1.53  #Tautology    : 78
% 3.18/1.53  #SimpNegUnit  : 0
% 3.18/1.53  #BackRed      : 1
% 3.18/1.53  
% 3.18/1.53  #Partial instantiations: 0
% 3.18/1.53  #Strategies tried      : 1
% 3.18/1.53  
% 3.18/1.53  Timing (in seconds)
% 3.18/1.53  ----------------------
% 3.38/1.53  Preprocessing        : 0.28
% 3.38/1.53  Parsing              : 0.14
% 3.38/1.53  CNF conversion       : 0.02
% 3.38/1.53  Main loop            : 0.48
% 3.38/1.53  Inferencing          : 0.16
% 3.38/1.53  Reduction            : 0.22
% 3.38/1.53  Demodulation         : 0.19
% 3.38/1.53  BG Simplification    : 0.03
% 3.38/1.53  Subsumption          : 0.05
% 3.38/1.53  Abstraction          : 0.04
% 3.38/1.53  MUC search           : 0.00
% 3.38/1.53  Cooper               : 0.00
% 3.38/1.53  Total                : 0.79
% 3.38/1.53  Index Insertion      : 0.00
% 3.38/1.53  Index Deletion       : 0.00
% 3.38/1.53  Index Matching       : 0.00
% 3.38/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
