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
% DateTime   : Thu Dec  3 09:43:02 EST 2020

% Result     : Theorem 5.12s
% Output     : CNFRefutation 5.12s
% Verified   : 
% Statistics : Number of formulae       :   43 (  85 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  76 expanded)
%              Number of equality atoms :   33 (  75 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    5 (   3 average)

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
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(A_1,C_3)) = k4_xboole_0(A_1,k3_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_190,plain,(
    ! [A_28,B_29,C_30] : k2_xboole_0(k4_xboole_0(A_28,B_29),k4_xboole_0(A_28,C_30)) = k4_xboole_0(A_28,k3_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_214,plain,(
    ! [A_7,B_29,B_8] : k4_xboole_0(A_7,k3_xboole_0(B_29,k3_xboole_0(A_7,B_8))) = k2_xboole_0(k4_xboole_0(A_7,B_29),k4_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_190])).

tff(c_228,plain,(
    ! [A_7,B_29,B_8] : k4_xboole_0(A_7,k3_xboole_0(B_29,k3_xboole_0(A_7,B_8))) = k4_xboole_0(A_7,k3_xboole_0(B_29,B_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_214])).

tff(c_8,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_220,plain,(
    ! [A_9,B_29,B_10] : k4_xboole_0(A_9,k3_xboole_0(B_29,k4_xboole_0(A_9,B_10))) = k2_xboole_0(k4_xboole_0(A_9,B_29),k3_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_190])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k3_xboole_0(A_20,B_21),C_22) = k3_xboole_0(A_20,k4_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1840,plain,(
    ! [A_74,B_75,C_76] : k4_xboole_0(k3_xboole_0(A_74,B_75),k3_xboole_0(A_74,k4_xboole_0(B_75,C_76))) = k3_xboole_0(k3_xboole_0(A_74,B_75),C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_8])).

tff(c_1955,plain,(
    ! [A_11,B_12,C_76] : k3_xboole_0(A_11,k4_xboole_0(B_12,k3_xboole_0(A_11,k4_xboole_0(B_12,C_76)))) = k3_xboole_0(k3_xboole_0(A_11,B_12),C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1840])).

tff(c_3459,plain,(
    ! [A_11,B_12,C_76] : k3_xboole_0(A_11,k2_xboole_0(k4_xboole_0(B_12,A_11),k3_xboole_0(B_12,C_76))) = k3_xboole_0(k3_xboole_0(A_11,B_12),C_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_1955])).

tff(c_211,plain,(
    ! [A_7,B_8,C_30] : k4_xboole_0(A_7,k3_xboole_0(k3_xboole_0(A_7,B_8),C_30)) = k2_xboole_0(k4_xboole_0(A_7,B_8),k4_xboole_0(A_7,C_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_190])).

tff(c_540,plain,(
    ! [A_43,B_44,C_45] : k4_xboole_0(A_43,k3_xboole_0(k3_xboole_0(A_43,B_44),C_45)) = k4_xboole_0(A_43,k3_xboole_0(B_44,C_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_211])).

tff(c_576,plain,(
    ! [A_43,B_44,C_45] : k4_xboole_0(A_43,k4_xboole_0(A_43,k3_xboole_0(B_44,C_45))) = k3_xboole_0(A_43,k3_xboole_0(k3_xboole_0(A_43,B_44),C_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_8])).

tff(c_616,plain,(
    ! [A_43,B_44,C_45] : k3_xboole_0(A_43,k3_xboole_0(k3_xboole_0(A_43,B_44),C_45)) = k3_xboole_0(A_43,k3_xboole_0(B_44,C_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_576])).

tff(c_3460,plain,(
    ! [A_99,B_100,C_101] : k3_xboole_0(A_99,k2_xboole_0(k4_xboole_0(B_100,A_99),k3_xboole_0(B_100,C_101))) = k3_xboole_0(k3_xboole_0(A_99,B_100),C_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_1955])).

tff(c_29,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,k3_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_8])).

tff(c_40,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_35])).

tff(c_3529,plain,(
    ! [A_99,B_100,C_101] : k3_xboole_0(A_99,k2_xboole_0(k4_xboole_0(B_100,A_99),k3_xboole_0(B_100,C_101))) = k3_xboole_0(A_99,k3_xboole_0(k3_xboole_0(A_99,B_100),C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3460,c_40])).

tff(c_3638,plain,(
    ! [A_99,B_100,C_101] : k3_xboole_0(k3_xboole_0(A_99,B_100),C_101) = k3_xboole_0(A_99,k3_xboole_0(B_100,C_101)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3459,c_616,c_3529])).

tff(c_87,plain,(
    ! [A_20,B_21,B_8] : k3_xboole_0(A_20,k4_xboole_0(B_21,k3_xboole_0(k3_xboole_0(A_20,B_21),B_8))) = k4_xboole_0(k3_xboole_0(A_20,B_21),B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_63])).

tff(c_97,plain,(
    ! [A_20,B_21,B_8] : k3_xboole_0(A_20,k4_xboole_0(B_21,k3_xboole_0(k3_xboole_0(A_20,B_21),B_8))) = k3_xboole_0(A_20,k4_xboole_0(B_21,B_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_87])).

tff(c_3660,plain,(
    ! [A_20,B_21,B_8] : k3_xboole_0(A_20,k4_xboole_0(B_21,k3_xboole_0(A_20,k3_xboole_0(B_21,B_8)))) = k3_xboole_0(A_20,k4_xboole_0(B_21,B_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3638,c_97])).

tff(c_3663,plain,(
    ! [A_20,B_21,B_8] : k3_xboole_0(A_20,k4_xboole_0(B_21,k3_xboole_0(A_20,B_8))) = k3_xboole_0(A_20,k4_xboole_0(B_21,B_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_3660])).

tff(c_12,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3'))) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_4518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3663,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:38:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.12/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/1.99  
% 5.12/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/1.99  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 5.12/1.99  
% 5.12/1.99  %Foreground sorts:
% 5.12/1.99  
% 5.12/1.99  
% 5.12/1.99  %Background operators:
% 5.12/1.99  
% 5.12/1.99  
% 5.12/1.99  %Foreground operators:
% 5.12/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.12/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.12/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.12/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.12/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.12/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.12/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.12/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.12/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.12/1.99  
% 5.12/2.00  tff(f_27, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 5.12/2.00  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.12/2.00  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.12/2.00  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.12/2.00  tff(f_38, negated_conjecture, ~(![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 5.12/2.00  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(A_1, C_3))=k4_xboole_0(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.12/2.00  tff(c_6, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.12/2.00  tff(c_190, plain, (![A_28, B_29, C_30]: (k2_xboole_0(k4_xboole_0(A_28, B_29), k4_xboole_0(A_28, C_30))=k4_xboole_0(A_28, k3_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.12/2.00  tff(c_214, plain, (![A_7, B_29, B_8]: (k4_xboole_0(A_7, k3_xboole_0(B_29, k3_xboole_0(A_7, B_8)))=k2_xboole_0(k4_xboole_0(A_7, B_29), k4_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_190])).
% 5.12/2.00  tff(c_228, plain, (![A_7, B_29, B_8]: (k4_xboole_0(A_7, k3_xboole_0(B_29, k3_xboole_0(A_7, B_8)))=k4_xboole_0(A_7, k3_xboole_0(B_29, B_8)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_214])).
% 5.12/2.00  tff(c_8, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.12/2.00  tff(c_220, plain, (![A_9, B_29, B_10]: (k4_xboole_0(A_9, k3_xboole_0(B_29, k4_xboole_0(A_9, B_10)))=k2_xboole_0(k4_xboole_0(A_9, B_29), k3_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_190])).
% 5.12/2.00  tff(c_10, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.12/2.00  tff(c_63, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k3_xboole_0(A_20, B_21), C_22)=k3_xboole_0(A_20, k4_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.12/2.00  tff(c_1840, plain, (![A_74, B_75, C_76]: (k4_xboole_0(k3_xboole_0(A_74, B_75), k3_xboole_0(A_74, k4_xboole_0(B_75, C_76)))=k3_xboole_0(k3_xboole_0(A_74, B_75), C_76))), inference(superposition, [status(thm), theory('equality')], [c_63, c_8])).
% 5.12/2.00  tff(c_1955, plain, (![A_11, B_12, C_76]: (k3_xboole_0(A_11, k4_xboole_0(B_12, k3_xboole_0(A_11, k4_xboole_0(B_12, C_76))))=k3_xboole_0(k3_xboole_0(A_11, B_12), C_76))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1840])).
% 5.12/2.00  tff(c_3459, plain, (![A_11, B_12, C_76]: (k3_xboole_0(A_11, k2_xboole_0(k4_xboole_0(B_12, A_11), k3_xboole_0(B_12, C_76)))=k3_xboole_0(k3_xboole_0(A_11, B_12), C_76))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_1955])).
% 5.12/2.00  tff(c_211, plain, (![A_7, B_8, C_30]: (k4_xboole_0(A_7, k3_xboole_0(k3_xboole_0(A_7, B_8), C_30))=k2_xboole_0(k4_xboole_0(A_7, B_8), k4_xboole_0(A_7, C_30)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_190])).
% 5.12/2.00  tff(c_540, plain, (![A_43, B_44, C_45]: (k4_xboole_0(A_43, k3_xboole_0(k3_xboole_0(A_43, B_44), C_45))=k4_xboole_0(A_43, k3_xboole_0(B_44, C_45)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_211])).
% 5.12/2.00  tff(c_576, plain, (![A_43, B_44, C_45]: (k4_xboole_0(A_43, k4_xboole_0(A_43, k3_xboole_0(B_44, C_45)))=k3_xboole_0(A_43, k3_xboole_0(k3_xboole_0(A_43, B_44), C_45)))), inference(superposition, [status(thm), theory('equality')], [c_540, c_8])).
% 5.12/2.00  tff(c_616, plain, (![A_43, B_44, C_45]: (k3_xboole_0(A_43, k3_xboole_0(k3_xboole_0(A_43, B_44), C_45))=k3_xboole_0(A_43, k3_xboole_0(B_44, C_45)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_576])).
% 5.12/2.00  tff(c_3460, plain, (![A_99, B_100, C_101]: (k3_xboole_0(A_99, k2_xboole_0(k4_xboole_0(B_100, A_99), k3_xboole_0(B_100, C_101)))=k3_xboole_0(k3_xboole_0(A_99, B_100), C_101))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_1955])).
% 5.12/2.00  tff(c_29, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.12/2.00  tff(c_35, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, k3_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_29, c_8])).
% 5.12/2.00  tff(c_40, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_35])).
% 5.12/2.00  tff(c_3529, plain, (![A_99, B_100, C_101]: (k3_xboole_0(A_99, k2_xboole_0(k4_xboole_0(B_100, A_99), k3_xboole_0(B_100, C_101)))=k3_xboole_0(A_99, k3_xboole_0(k3_xboole_0(A_99, B_100), C_101)))), inference(superposition, [status(thm), theory('equality')], [c_3460, c_40])).
% 5.12/2.00  tff(c_3638, plain, (![A_99, B_100, C_101]: (k3_xboole_0(k3_xboole_0(A_99, B_100), C_101)=k3_xboole_0(A_99, k3_xboole_0(B_100, C_101)))), inference(demodulation, [status(thm), theory('equality')], [c_3459, c_616, c_3529])).
% 5.12/2.00  tff(c_87, plain, (![A_20, B_21, B_8]: (k3_xboole_0(A_20, k4_xboole_0(B_21, k3_xboole_0(k3_xboole_0(A_20, B_21), B_8)))=k4_xboole_0(k3_xboole_0(A_20, B_21), B_8))), inference(superposition, [status(thm), theory('equality')], [c_6, c_63])).
% 5.12/2.00  tff(c_97, plain, (![A_20, B_21, B_8]: (k3_xboole_0(A_20, k4_xboole_0(B_21, k3_xboole_0(k3_xboole_0(A_20, B_21), B_8)))=k3_xboole_0(A_20, k4_xboole_0(B_21, B_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_87])).
% 5.12/2.00  tff(c_3660, plain, (![A_20, B_21, B_8]: (k3_xboole_0(A_20, k4_xboole_0(B_21, k3_xboole_0(A_20, k3_xboole_0(B_21, B_8))))=k3_xboole_0(A_20, k4_xboole_0(B_21, B_8)))), inference(demodulation, [status(thm), theory('equality')], [c_3638, c_97])).
% 5.12/2.00  tff(c_3663, plain, (![A_20, B_21, B_8]: (k3_xboole_0(A_20, k4_xboole_0(B_21, k3_xboole_0(A_20, B_8)))=k3_xboole_0(A_20, k4_xboole_0(B_21, B_8)))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_3660])).
% 5.12/2.00  tff(c_12, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.12/2.00  tff(c_13, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_3')))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 5.12/2.00  tff(c_4518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3663, c_13])).
% 5.12/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/2.00  
% 5.12/2.00  Inference rules
% 5.12/2.00  ----------------------
% 5.12/2.00  #Ref     : 0
% 5.12/2.00  #Sup     : 1073
% 5.12/2.00  #Fact    : 0
% 5.12/2.00  #Define  : 0
% 5.12/2.00  #Split   : 0
% 5.12/2.00  #Chain   : 0
% 5.12/2.00  #Close   : 0
% 5.12/2.00  
% 5.12/2.00  Ordering : KBO
% 5.12/2.00  
% 5.12/2.00  Simplification rules
% 5.12/2.00  ----------------------
% 5.12/2.00  #Subsume      : 0
% 5.12/2.00  #Demod        : 2038
% 5.12/2.00  #Tautology    : 491
% 5.12/2.00  #SimpNegUnit  : 0
% 5.12/2.00  #BackRed      : 9
% 5.12/2.00  
% 5.12/2.00  #Partial instantiations: 0
% 5.12/2.00  #Strategies tried      : 1
% 5.12/2.00  
% 5.12/2.00  Timing (in seconds)
% 5.12/2.00  ----------------------
% 5.12/2.00  Preprocessing        : 0.25
% 5.12/2.00  Parsing              : 0.13
% 5.12/2.00  CNF conversion       : 0.01
% 5.12/2.00  Main loop            : 0.92
% 5.12/2.00  Inferencing          : 0.30
% 5.12/2.00  Reduction            : 0.45
% 5.12/2.00  Demodulation         : 0.38
% 5.12/2.00  BG Simplification    : 0.05
% 5.12/2.00  Subsumption          : 0.09
% 5.12/2.01  Abstraction          : 0.09
% 5.12/2.01  MUC search           : 0.00
% 5.12/2.01  Cooper               : 0.00
% 5.12/2.01  Total                : 1.20
% 5.12/2.01  Index Insertion      : 0.00
% 5.12/2.01  Index Deletion       : 0.00
% 5.12/2.01  Index Matching       : 0.00
% 5.12/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
