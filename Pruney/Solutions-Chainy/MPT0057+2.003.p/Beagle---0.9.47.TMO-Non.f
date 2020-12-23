%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:02 EST 2020

% Result     : Timeout 59.32s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   38 (  52 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  41 expanded)
%              Number of equality atoms :   26 (  40 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_57,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(c_30,plain,(
    ! [A_28,B_29,C_30] : k4_xboole_0(k3_xboole_0(A_28,B_29),C_30) = k3_xboole_0(A_28,k4_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_670,plain,(
    ! [A_69,B_70,C_71] : k4_xboole_0(k4_xboole_0(A_69,B_70),C_71) = k4_xboole_0(A_69,k2_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_728,plain,(
    ! [A_26,B_27,C_71] : k4_xboole_0(A_26,k2_xboole_0(k4_xboole_0(A_26,B_27),C_71)) = k4_xboole_0(k3_xboole_0(A_26,B_27),C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_670])).

tff(c_31686,plain,(
    ! [A_26,B_27,C_71] : k4_xboole_0(A_26,k2_xboole_0(k4_xboole_0(A_26,B_27),C_71)) = k3_xboole_0(A_26,k4_xboole_0(B_27,C_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_728])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k3_xboole_0(k2_xboole_0(A_6,B_7),k2_xboole_0(A_6,C_8)) = k2_xboole_0(A_6,k3_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1969,plain,(
    ! [A_97,B_98,C_99] : k3_xboole_0(k2_xboole_0(A_97,B_98),k2_xboole_0(A_97,C_99)) = k2_xboole_0(A_97,k3_xboole_0(B_98,C_99)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2028,plain,(
    ! [A_14,B_15,C_99] : k3_xboole_0(k2_xboole_0(A_14,B_15),k2_xboole_0(A_14,C_99)) = k2_xboole_0(A_14,k3_xboole_0(k4_xboole_0(B_15,A_14),C_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1969])).

tff(c_2091,plain,(
    ! [A_14,B_15,C_99] : k2_xboole_0(A_14,k3_xboole_0(k4_xboole_0(B_15,A_14),C_99)) = k2_xboole_0(A_14,k3_xboole_0(B_15,C_99)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2028])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k4_xboole_0(A_16,B_17),C_18) = k4_xboole_0(A_16,k2_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_739,plain,(
    ! [A_69,B_70,B_25] : k4_xboole_0(A_69,k2_xboole_0(B_70,k3_xboole_0(k4_xboole_0(A_69,B_70),B_25))) = k4_xboole_0(k4_xboole_0(A_69,B_70),B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_670])).

tff(c_776,plain,(
    ! [A_69,B_70,B_25] : k4_xboole_0(A_69,k2_xboole_0(B_70,k3_xboole_0(k4_xboole_0(A_69,B_70),B_25))) = k4_xboole_0(A_69,k2_xboole_0(B_70,B_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_739])).

tff(c_43144,plain,(
    ! [A_393,B_394,B_395] : k4_xboole_0(A_393,k2_xboole_0(B_394,k3_xboole_0(A_393,B_395))) = k4_xboole_0(A_393,k2_xboole_0(B_394,B_395)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2091,c_776])).

tff(c_43439,plain,(
    ! [A_26,B_27,B_395] : k4_xboole_0(A_26,k2_xboole_0(k4_xboole_0(A_26,B_27),B_395)) = k3_xboole_0(A_26,k4_xboole_0(B_27,k3_xboole_0(A_26,B_395))) ),
    inference(superposition,[status(thm),theory(equality)],[c_31686,c_43144])).

tff(c_43744,plain,(
    ! [A_26,B_27,B_395] : k3_xboole_0(A_26,k4_xboole_0(B_27,k3_xboole_0(A_26,B_395))) = k3_xboole_0(A_26,k4_xboole_0(B_27,B_395)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31686,c_43439])).

tff(c_36,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_37,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',k3_xboole_0('#skF_1','#skF_3'))) != k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36])).

tff(c_189464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43744,c_37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 59.32/47.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.32/47.79  
% 59.32/47.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.32/47.79  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 59.32/47.79  
% 59.32/47.79  %Foreground sorts:
% 59.32/47.79  
% 59.32/47.79  
% 59.32/47.79  %Background operators:
% 59.32/47.79  
% 59.32/47.79  
% 59.32/47.79  %Foreground operators:
% 59.32/47.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 59.32/47.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 59.32/47.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 59.32/47.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 59.32/47.79  tff('#skF_2', type, '#skF_2': $i).
% 59.32/47.79  tff('#skF_3', type, '#skF_3': $i).
% 59.32/47.79  tff('#skF_1', type, '#skF_1': $i).
% 59.32/47.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 59.32/47.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 59.32/47.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 59.32/47.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 59.32/47.79  
% 59.32/47.80  tff(f_57, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 59.32/47.80  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 59.32/47.80  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 59.32/47.80  tff(f_33, axiom, (![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 59.32/47.80  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 59.32/47.80  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 59.32/47.80  tff(f_64, negated_conjecture, ~(![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 59.32/47.80  tff(c_30, plain, (![A_28, B_29, C_30]: (k4_xboole_0(k3_xboole_0(A_28, B_29), C_30)=k3_xboole_0(A_28, k4_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 59.32/47.80  tff(c_28, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 59.32/47.80  tff(c_670, plain, (![A_69, B_70, C_71]: (k4_xboole_0(k4_xboole_0(A_69, B_70), C_71)=k4_xboole_0(A_69, k2_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 59.32/47.80  tff(c_728, plain, (![A_26, B_27, C_71]: (k4_xboole_0(A_26, k2_xboole_0(k4_xboole_0(A_26, B_27), C_71))=k4_xboole_0(k3_xboole_0(A_26, B_27), C_71))), inference(superposition, [status(thm), theory('equality')], [c_28, c_670])).
% 59.32/47.80  tff(c_31686, plain, (![A_26, B_27, C_71]: (k4_xboole_0(A_26, k2_xboole_0(k4_xboole_0(A_26, B_27), C_71))=k3_xboole_0(A_26, k4_xboole_0(B_27, C_71)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_728])).
% 59.32/47.80  tff(c_8, plain, (![A_6, B_7, C_8]: (k3_xboole_0(k2_xboole_0(A_6, B_7), k2_xboole_0(A_6, C_8))=k2_xboole_0(A_6, k3_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 59.32/47.80  tff(c_18, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 59.32/47.80  tff(c_1969, plain, (![A_97, B_98, C_99]: (k3_xboole_0(k2_xboole_0(A_97, B_98), k2_xboole_0(A_97, C_99))=k2_xboole_0(A_97, k3_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 59.32/47.80  tff(c_2028, plain, (![A_14, B_15, C_99]: (k3_xboole_0(k2_xboole_0(A_14, B_15), k2_xboole_0(A_14, C_99))=k2_xboole_0(A_14, k3_xboole_0(k4_xboole_0(B_15, A_14), C_99)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1969])).
% 59.32/47.80  tff(c_2091, plain, (![A_14, B_15, C_99]: (k2_xboole_0(A_14, k3_xboole_0(k4_xboole_0(B_15, A_14), C_99))=k2_xboole_0(A_14, k3_xboole_0(B_15, C_99)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2028])).
% 59.32/47.80  tff(c_20, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k4_xboole_0(A_16, B_17), C_18)=k4_xboole_0(A_16, k2_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 59.32/47.80  tff(c_26, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 59.32/47.80  tff(c_739, plain, (![A_69, B_70, B_25]: (k4_xboole_0(A_69, k2_xboole_0(B_70, k3_xboole_0(k4_xboole_0(A_69, B_70), B_25)))=k4_xboole_0(k4_xboole_0(A_69, B_70), B_25))), inference(superposition, [status(thm), theory('equality')], [c_26, c_670])).
% 59.32/47.80  tff(c_776, plain, (![A_69, B_70, B_25]: (k4_xboole_0(A_69, k2_xboole_0(B_70, k3_xboole_0(k4_xboole_0(A_69, B_70), B_25)))=k4_xboole_0(A_69, k2_xboole_0(B_70, B_25)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_739])).
% 59.32/47.80  tff(c_43144, plain, (![A_393, B_394, B_395]: (k4_xboole_0(A_393, k2_xboole_0(B_394, k3_xboole_0(A_393, B_395)))=k4_xboole_0(A_393, k2_xboole_0(B_394, B_395)))), inference(demodulation, [status(thm), theory('equality')], [c_2091, c_776])).
% 59.32/47.80  tff(c_43439, plain, (![A_26, B_27, B_395]: (k4_xboole_0(A_26, k2_xboole_0(k4_xboole_0(A_26, B_27), B_395))=k3_xboole_0(A_26, k4_xboole_0(B_27, k3_xboole_0(A_26, B_395))))), inference(superposition, [status(thm), theory('equality')], [c_31686, c_43144])).
% 59.32/47.80  tff(c_43744, plain, (![A_26, B_27, B_395]: (k3_xboole_0(A_26, k4_xboole_0(B_27, k3_xboole_0(A_26, B_395)))=k3_xboole_0(A_26, k4_xboole_0(B_27, B_395)))), inference(demodulation, [status(thm), theory('equality')], [c_31686, c_43439])).
% 59.32/47.80  tff(c_36, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 59.32/47.80  tff(c_37, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', k3_xboole_0('#skF_1', '#skF_3')))!=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36])).
% 59.32/47.80  tff(c_189464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43744, c_37])).
% 59.32/47.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.32/47.80  
% 59.32/47.80  Inference rules
% 59.32/47.80  ----------------------
% 59.32/47.80  #Ref     : 5
% 59.32/47.80  #Sup     : 49626
% 59.32/47.80  #Fact    : 0
% 59.32/47.80  #Define  : 0
% 59.32/47.80  #Split   : 6
% 59.32/47.80  #Chain   : 0
% 59.32/47.80  #Close   : 0
% 59.32/47.80  
% 59.32/47.80  Ordering : KBO
% 59.32/47.80  
% 59.32/47.80  Simplification rules
% 59.32/47.80  ----------------------
% 59.32/47.80  #Subsume      : 6205
% 59.32/47.80  #Demod        : 58810
% 59.32/47.80  #Tautology    : 21978
% 59.32/47.80  #SimpNegUnit  : 0
% 59.32/47.80  #BackRed      : 6
% 59.32/47.80  
% 59.32/47.80  #Partial instantiations: 0
% 59.32/47.80  #Strategies tried      : 1
% 59.32/47.80  
% 59.32/47.80  Timing (in seconds)
% 59.32/47.80  ----------------------
% 59.32/47.81  Preprocessing        : 0.47
% 59.32/47.81  Parsing              : 0.25
% 59.32/47.81  CNF conversion       : 0.03
% 59.32/47.81  Main loop            : 46.42
% 59.32/47.81  Inferencing          : 3.80
% 59.32/47.81  Reduction            : 33.58
% 59.32/47.81  Demodulation         : 31.89
% 59.32/47.81  BG Simplification    : 0.64
% 59.32/47.81  Subsumption          : 6.90
% 59.32/47.81  Abstraction          : 1.20
% 59.32/47.81  MUC search           : 0.00
% 59.32/47.81  Cooper               : 0.00
% 59.32/47.81  Total                : 46.93
% 59.32/47.81  Index Insertion      : 0.00
% 59.32/47.81  Index Deletion       : 0.00
% 59.32/47.81  Index Matching       : 0.00
% 59.32/47.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
