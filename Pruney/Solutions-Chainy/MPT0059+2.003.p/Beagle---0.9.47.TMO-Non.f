%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:04 EST 2020

% Result     : Timeout 58.54s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   45 (  63 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  54 expanded)
%              Number of equality atoms :   35 (  53 expanded)
%              Maximal formula depth    :    5 (   3 average)
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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_14,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k3_xboole_0(A_20,B_21),C_22) = k3_xboole_0(A_20,k4_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [A_37,B_38] : k4_xboole_0(k2_xboole_0(A_37,B_38),B_38) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_155,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_128])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k3_xboole_0(k2_xboole_0(A_6,B_7),k2_xboole_0(A_6,C_8)) = k2_xboole_0(A_6,k3_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_732,plain,(
    ! [A_62,B_63,C_64] : k3_xboole_0(k2_xboole_0(A_62,B_63),k2_xboole_0(A_62,C_64)) = k2_xboole_0(A_62,k3_xboole_0(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_795,plain,(
    ! [A_9,B_10,C_64] : k3_xboole_0(k2_xboole_0(A_9,B_10),k2_xboole_0(A_9,C_64)) = k2_xboole_0(A_9,k3_xboole_0(k4_xboole_0(B_10,A_9),C_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_732])).

tff(c_14690,plain,(
    ! [A_215,B_216,C_217] : k2_xboole_0(A_215,k3_xboole_0(k4_xboole_0(B_216,A_215),C_217)) = k2_xboole_0(A_215,k3_xboole_0(B_216,C_217)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_795])).

tff(c_14786,plain,(
    ! [B_216,A_215,C_217] : k4_xboole_0(k3_xboole_0(k4_xboole_0(B_216,A_215),C_217),A_215) = k4_xboole_0(k2_xboole_0(A_215,k3_xboole_0(B_216,C_217)),A_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_14690,c_155])).

tff(c_14988,plain,(
    ! [B_216,A_215,C_217] : k3_xboole_0(k4_xboole_0(B_216,A_215),k4_xboole_0(C_217,A_215)) = k3_xboole_0(B_216,k4_xboole_0(C_217,A_215)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_155,c_14786])).

tff(c_338,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(k4_xboole_0(A_48,B_49),C_50) = k4_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_353,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(k4_xboole_0(A_48,B_49),k4_xboole_0(A_48,k2_xboole_0(B_49,C_50))) = k3_xboole_0(k4_xboole_0(A_48,B_49),C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_16])).

tff(c_35315,plain,(
    ! [A_346,B_347,C_348] : k4_xboole_0(k4_xboole_0(A_346,B_347),k4_xboole_0(A_346,k2_xboole_0(B_347,C_348))) = k3_xboole_0(k4_xboole_0(A_346,B_347),C_348) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_16])).

tff(c_35867,plain,(
    ! [A_346,A_9,B_10] : k4_xboole_0(k4_xboole_0(A_346,A_9),k4_xboole_0(A_346,k2_xboole_0(A_9,B_10))) = k3_xboole_0(k4_xboole_0(A_346,A_9),k4_xboole_0(B_10,A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_35315])).

tff(c_36012,plain,(
    ! [A_346,A_9,B_10] : k3_xboole_0(k4_xboole_0(A_346,A_9),k4_xboole_0(B_10,A_9)) = k3_xboole_0(k4_xboole_0(A_346,A_9),B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_35867])).

tff(c_129069,plain,(
    ! [A_346,A_9,B_10] : k3_xboole_0(k4_xboole_0(A_346,A_9),B_10) = k3_xboole_0(A_346,k4_xboole_0(B_10,A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14988,c_36012])).

tff(c_933,plain,(
    ! [A_68,B_69,C_70] : k2_xboole_0(k4_xboole_0(A_68,B_69),k4_xboole_0(A_68,C_70)) = k4_xboole_0(A_68,k3_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1011,plain,(
    ! [A_18,B_19,C_70] : k4_xboole_0(A_18,k3_xboole_0(k4_xboole_0(A_18,B_19),C_70)) = k2_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_933])).

tff(c_129077,plain,(
    ! [A_18,C_70,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,k4_xboole_0(C_70,B_19))) = k2_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,C_70)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129069,c_1011])).

tff(c_129087,plain,(
    ! [A_18,B_19,C_70] : k2_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,C_70)) = k4_xboole_0(A_18,k4_xboole_0(C_70,B_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_129077])).

tff(c_22,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_23,plain,(
    k2_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k4_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_203693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129087,c_23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 58.54/48.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.54/48.79  
% 58.54/48.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.54/48.80  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 58.54/48.80  
% 58.54/48.80  %Foreground sorts:
% 58.54/48.80  
% 58.54/48.80  
% 58.54/48.80  %Background operators:
% 58.54/48.80  
% 58.54/48.80  
% 58.54/48.80  %Foreground operators:
% 58.54/48.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 58.54/48.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 58.54/48.80  tff('#skF_2', type, '#skF_2': $i).
% 58.54/48.80  tff('#skF_3', type, '#skF_3': $i).
% 58.54/48.80  tff('#skF_1', type, '#skF_1': $i).
% 58.54/48.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 58.54/48.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 58.54/48.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 58.54/48.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 58.54/48.80  
% 58.58/48.81  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 58.58/48.81  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 58.58/48.81  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 58.58/48.81  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 58.58/48.81  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 58.58/48.81  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 58.58/48.81  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 58.58/48.81  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 58.58/48.81  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 58.58/48.81  tff(f_48, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 58.58/48.81  tff(c_14, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 58.58/48.81  tff(c_18, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k3_xboole_0(A_20, B_21), C_22)=k3_xboole_0(A_20, k4_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 58.58/48.81  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 58.58/48.81  tff(c_128, plain, (![A_37, B_38]: (k4_xboole_0(k2_xboole_0(A_37, B_38), B_38)=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 58.58/48.81  tff(c_155, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_128])).
% 58.58/48.81  tff(c_6, plain, (![A_6, B_7, C_8]: (k3_xboole_0(k2_xboole_0(A_6, B_7), k2_xboole_0(A_6, C_8))=k2_xboole_0(A_6, k3_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 58.58/48.81  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 58.58/48.81  tff(c_732, plain, (![A_62, B_63, C_64]: (k3_xboole_0(k2_xboole_0(A_62, B_63), k2_xboole_0(A_62, C_64))=k2_xboole_0(A_62, k3_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 58.58/48.81  tff(c_795, plain, (![A_9, B_10, C_64]: (k3_xboole_0(k2_xboole_0(A_9, B_10), k2_xboole_0(A_9, C_64))=k2_xboole_0(A_9, k3_xboole_0(k4_xboole_0(B_10, A_9), C_64)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_732])).
% 58.58/48.81  tff(c_14690, plain, (![A_215, B_216, C_217]: (k2_xboole_0(A_215, k3_xboole_0(k4_xboole_0(B_216, A_215), C_217))=k2_xboole_0(A_215, k3_xboole_0(B_216, C_217)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_795])).
% 58.58/48.81  tff(c_14786, plain, (![B_216, A_215, C_217]: (k4_xboole_0(k3_xboole_0(k4_xboole_0(B_216, A_215), C_217), A_215)=k4_xboole_0(k2_xboole_0(A_215, k3_xboole_0(B_216, C_217)), A_215))), inference(superposition, [status(thm), theory('equality')], [c_14690, c_155])).
% 58.58/48.81  tff(c_14988, plain, (![B_216, A_215, C_217]: (k3_xboole_0(k4_xboole_0(B_216, A_215), k4_xboole_0(C_217, A_215))=k3_xboole_0(B_216, k4_xboole_0(C_217, A_215)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_155, c_14786])).
% 58.58/48.81  tff(c_338, plain, (![A_48, B_49, C_50]: (k4_xboole_0(k4_xboole_0(A_48, B_49), C_50)=k4_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 58.58/48.81  tff(c_16, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 58.58/48.81  tff(c_353, plain, (![A_48, B_49, C_50]: (k4_xboole_0(k4_xboole_0(A_48, B_49), k4_xboole_0(A_48, k2_xboole_0(B_49, C_50)))=k3_xboole_0(k4_xboole_0(A_48, B_49), C_50))), inference(superposition, [status(thm), theory('equality')], [c_338, c_16])).
% 58.58/48.81  tff(c_35315, plain, (![A_346, B_347, C_348]: (k4_xboole_0(k4_xboole_0(A_346, B_347), k4_xboole_0(A_346, k2_xboole_0(B_347, C_348)))=k3_xboole_0(k4_xboole_0(A_346, B_347), C_348))), inference(superposition, [status(thm), theory('equality')], [c_338, c_16])).
% 58.58/48.81  tff(c_35867, plain, (![A_346, A_9, B_10]: (k4_xboole_0(k4_xboole_0(A_346, A_9), k4_xboole_0(A_346, k2_xboole_0(A_9, B_10)))=k3_xboole_0(k4_xboole_0(A_346, A_9), k4_xboole_0(B_10, A_9)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_35315])).
% 58.58/48.81  tff(c_36012, plain, (![A_346, A_9, B_10]: (k3_xboole_0(k4_xboole_0(A_346, A_9), k4_xboole_0(B_10, A_9))=k3_xboole_0(k4_xboole_0(A_346, A_9), B_10))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_35867])).
% 58.58/48.81  tff(c_129069, plain, (![A_346, A_9, B_10]: (k3_xboole_0(k4_xboole_0(A_346, A_9), B_10)=k3_xboole_0(A_346, k4_xboole_0(B_10, A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_14988, c_36012])).
% 58.58/48.81  tff(c_933, plain, (![A_68, B_69, C_70]: (k2_xboole_0(k4_xboole_0(A_68, B_69), k4_xboole_0(A_68, C_70))=k4_xboole_0(A_68, k3_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 58.58/48.81  tff(c_1011, plain, (![A_18, B_19, C_70]: (k4_xboole_0(A_18, k3_xboole_0(k4_xboole_0(A_18, B_19), C_70))=k2_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, C_70)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_933])).
% 58.58/48.81  tff(c_129077, plain, (![A_18, C_70, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, k4_xboole_0(C_70, B_19)))=k2_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, C_70)))), inference(demodulation, [status(thm), theory('equality')], [c_129069, c_1011])).
% 58.58/48.81  tff(c_129087, plain, (![A_18, B_19, C_70]: (k2_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, C_70))=k4_xboole_0(A_18, k4_xboole_0(C_70, B_19)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_129077])).
% 58.58/48.81  tff(c_22, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 58.58/48.81  tff(c_23, plain, (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k4_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 58.58/48.81  tff(c_203693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129087, c_23])).
% 58.58/48.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.58/48.81  
% 58.58/48.81  Inference rules
% 58.58/48.81  ----------------------
% 58.58/48.81  #Ref     : 0
% 58.58/48.81  #Sup     : 51911
% 58.58/48.81  #Fact    : 0
% 58.58/48.81  #Define  : 0
% 58.58/48.81  #Split   : 0
% 58.58/48.81  #Chain   : 0
% 58.58/48.81  #Close   : 0
% 58.58/48.81  
% 58.58/48.81  Ordering : KBO
% 58.58/48.81  
% 58.58/48.81  Simplification rules
% 58.58/48.81  ----------------------
% 58.58/48.81  #Subsume      : 5362
% 58.58/48.81  #Demod        : 72029
% 58.58/48.81  #Tautology    : 20997
% 58.58/48.81  #SimpNegUnit  : 0
% 58.58/48.81  #BackRed      : 43
% 58.58/48.81  
% 58.58/48.81  #Partial instantiations: 0
% 58.58/48.81  #Strategies tried      : 1
% 58.58/48.81  
% 58.58/48.81  Timing (in seconds)
% 58.58/48.81  ----------------------
% 58.58/48.81  Preprocessing        : 0.29
% 58.58/48.81  Parsing              : 0.16
% 58.58/48.81  CNF conversion       : 0.02
% 58.58/48.81  Main loop            : 47.76
% 58.58/48.81  Inferencing          : 4.24
% 58.58/48.81  Reduction            : 34.10
% 58.58/48.81  Demodulation         : 32.67
% 58.58/48.81  BG Simplification    : 0.70
% 58.58/48.81  Subsumption          : 7.42
% 58.58/48.81  Abstraction          : 1.51
% 58.58/48.81  MUC search           : 0.00
% 58.58/48.81  Cooper               : 0.00
% 58.58/48.81  Total                : 48.07
% 58.58/48.81  Index Insertion      : 0.00
% 58.58/48.81  Index Deletion       : 0.00
% 58.58/48.81  Index Matching       : 0.00
% 58.58/48.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
