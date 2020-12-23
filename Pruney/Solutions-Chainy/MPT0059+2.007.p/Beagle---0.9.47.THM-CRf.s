%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:05 EST 2020

% Result     : Theorem 5.31s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 129 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   46 ( 120 expanded)
%              Number of equality atoms :   45 ( 119 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    6 (   3 average)

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

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_8,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_234,plain,(
    ! [A_34,B_35,C_36] : k2_xboole_0(k4_xboole_0(A_34,B_35),k4_xboole_0(A_34,C_36)) = k4_xboole_0(A_34,k3_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_270,plain,(
    ! [A_9,B_35,B_10] : k4_xboole_0(A_9,k3_xboole_0(B_35,k4_xboole_0(A_9,B_10))) = k2_xboole_0(k4_xboole_0(A_9,B_35),k3_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_234])).

tff(c_6,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k3_xboole_0(A_11,B_12),C_13) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_152,plain,(
    ! [A_29,B_30,C_31] : k4_xboole_0(k3_xboole_0(A_29,B_30),k3_xboole_0(A_29,C_31)) = k3_xboole_0(A_29,k4_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_419,plain,(
    ! [A_43,B_44,C_45] : k3_xboole_0(A_43,k4_xboole_0(B_44,k3_xboole_0(A_43,C_45))) = k3_xboole_0(A_43,k4_xboole_0(B_44,C_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_152])).

tff(c_447,plain,(
    ! [A_43,B_44,C_45] : k4_xboole_0(A_43,k4_xboole_0(B_44,k3_xboole_0(A_43,C_45))) = k4_xboole_0(A_43,k3_xboole_0(A_43,k4_xboole_0(B_44,C_45))) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_6])).

tff(c_486,plain,(
    ! [A_43,B_44,C_45] : k4_xboole_0(A_43,k4_xboole_0(B_44,k3_xboole_0(A_43,C_45))) = k4_xboole_0(A_43,k4_xboole_0(B_44,C_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_447])).

tff(c_15,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_15])).

tff(c_183,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_24])).

tff(c_30,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,k3_xboole_0(A_19,B_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8])).

tff(c_41,plain,(
    ! [A_19,B_20] : k3_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36])).

tff(c_171,plain,(
    ! [A_11,B_12,C_31] : k3_xboole_0(A_11,k4_xboole_0(B_12,k3_xboole_0(A_11,C_31))) = k3_xboole_0(A_11,k4_xboole_0(B_12,C_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_152])).

tff(c_100,plain,(
    ! [A_26,B_27,C_28] : k4_xboole_0(k4_xboole_0(A_26,B_27),C_28) = k4_xboole_0(A_26,k2_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_136,plain,(
    ! [A_9,B_10,C_28] : k4_xboole_0(A_9,k2_xboole_0(k4_xboole_0(A_9,B_10),C_28)) = k4_xboole_0(k3_xboole_0(A_9,B_10),C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_100])).

tff(c_150,plain,(
    ! [A_9,B_10,C_28] : k4_xboole_0(A_9,k2_xboole_0(k4_xboole_0(A_9,B_10),C_28)) = k3_xboole_0(A_9,k4_xboole_0(B_10,C_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] : k4_xboole_0(k4_xboole_0(A_4,B_5),C_6) = k4_xboole_0(A_4,k2_xboole_0(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_140,plain,(
    ! [A_26,B_27,B_10] : k4_xboole_0(A_26,k2_xboole_0(B_27,k4_xboole_0(k4_xboole_0(A_26,B_27),B_10))) = k3_xboole_0(k4_xboole_0(A_26,B_27),B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_100])).

tff(c_1659,plain,(
    ! [A_76,B_77,B_78] : k4_xboole_0(A_76,k2_xboole_0(B_77,k4_xboole_0(A_76,k2_xboole_0(B_77,B_78)))) = k3_xboole_0(k4_xboole_0(A_76,B_77),B_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_140])).

tff(c_1684,plain,(
    ! [A_76,B_10,B_78] : k3_xboole_0(A_76,k4_xboole_0(B_10,k4_xboole_0(A_76,k2_xboole_0(k4_xboole_0(A_76,B_10),B_78)))) = k3_xboole_0(k4_xboole_0(A_76,k4_xboole_0(A_76,B_10)),B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_1659,c_150])).

tff(c_1757,plain,(
    ! [A_76,B_10,B_78] : k3_xboole_0(k3_xboole_0(A_76,B_10),B_78) = k3_xboole_0(A_76,k3_xboole_0(B_10,B_78)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_171,c_150,c_8,c_1684])).

tff(c_64,plain,(
    ! [A_23,B_24,C_25] : k4_xboole_0(k3_xboole_0(A_23,B_24),C_25) = k3_xboole_0(A_23,k4_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_23,B_24,C_25] : k4_xboole_0(k3_xboole_0(A_23,B_24),k3_xboole_0(A_23,k4_xboole_0(B_24,C_25))) = k3_xboole_0(k3_xboole_0(A_23,B_24),C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_8])).

tff(c_3672,plain,(
    ! [A_110,B_111,C_112] : k4_xboole_0(k3_xboole_0(A_110,B_111),k3_xboole_0(A_110,k4_xboole_0(B_111,C_112))) = k3_xboole_0(A_110,k3_xboole_0(B_111,C_112)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_74])).

tff(c_3823,plain,(
    ! [A_9,B_10] : k4_xboole_0(k3_xboole_0(A_9,A_9),k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,k3_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_3672])).

tff(c_3904,plain,(
    ! [A_113,B_114] : k4_xboole_0(k3_xboole_0(A_113,A_113),k4_xboole_0(A_113,B_114)) = k3_xboole_0(A_113,B_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_3823])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(A_1,C_3)) = k4_xboole_0(A_1,k3_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_338,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(A_40,k2_xboole_0(k4_xboole_0(A_40,B_41),C_42)) = k3_xboole_0(A_40,k4_xboole_0(B_41,C_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_379,plain,(
    ! [A_1,B_2,C_3] : k4_xboole_0(A_1,k4_xboole_0(A_1,k3_xboole_0(B_2,C_3))) = k3_xboole_0(A_1,k4_xboole_0(B_2,k4_xboole_0(A_1,C_3))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_338])).

tff(c_784,plain,(
    ! [A_55,B_56,C_57] : k3_xboole_0(A_55,k4_xboole_0(B_56,k4_xboole_0(A_55,C_57))) = k3_xboole_0(A_55,k3_xboole_0(B_56,C_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_379])).

tff(c_825,plain,(
    ! [A_55,B_56,C_57] : k4_xboole_0(A_55,k4_xboole_0(B_56,k4_xboole_0(A_55,C_57))) = k4_xboole_0(A_55,k3_xboole_0(A_55,k3_xboole_0(B_56,C_57))) ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_6])).

tff(c_889,plain,(
    ! [A_55,B_56,C_57] : k4_xboole_0(A_55,k4_xboole_0(B_56,k4_xboole_0(A_55,C_57))) = k4_xboole_0(A_55,k3_xboole_0(B_56,C_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_825])).

tff(c_3928,plain,(
    ! [A_113,B_56,B_114] : k4_xboole_0(k3_xboole_0(A_113,A_113),k4_xboole_0(B_56,k3_xboole_0(A_113,B_114))) = k4_xboole_0(k3_xboole_0(A_113,A_113),k3_xboole_0(B_56,k4_xboole_0(A_113,B_114))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3904,c_889])).

tff(c_4059,plain,(
    ! [A_113,B_56,B_114] : k2_xboole_0(k4_xboole_0(A_113,B_56),k3_xboole_0(A_113,B_114)) = k4_xboole_0(A_113,k4_xboole_0(B_56,B_114)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_486,c_183,c_183,c_10,c_10,c_3928])).

tff(c_14,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4059,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:59:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.31/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/2.01  
% 5.31/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/2.02  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 5.31/2.02  
% 5.31/2.02  %Foreground sorts:
% 5.31/2.02  
% 5.31/2.02  
% 5.31/2.02  %Background operators:
% 5.31/2.02  
% 5.31/2.02  
% 5.31/2.02  %Foreground operators:
% 5.31/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.31/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.31/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.31/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.31/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.31/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.31/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.31/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.31/2.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.31/2.02  
% 5.31/2.03  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.31/2.03  tff(f_27, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 5.31/2.03  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.31/2.03  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.31/2.03  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 5.31/2.03  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.31/2.03  tff(f_40, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 5.31/2.03  tff(c_8, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.31/2.03  tff(c_234, plain, (![A_34, B_35, C_36]: (k2_xboole_0(k4_xboole_0(A_34, B_35), k4_xboole_0(A_34, C_36))=k4_xboole_0(A_34, k3_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.31/2.03  tff(c_270, plain, (![A_9, B_35, B_10]: (k4_xboole_0(A_9, k3_xboole_0(B_35, k4_xboole_0(A_9, B_10)))=k2_xboole_0(k4_xboole_0(A_9, B_35), k3_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_234])).
% 5.31/2.03  tff(c_6, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.31/2.03  tff(c_10, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k3_xboole_0(A_11, B_12), C_13)=k3_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.31/2.03  tff(c_152, plain, (![A_29, B_30, C_31]: (k4_xboole_0(k3_xboole_0(A_29, B_30), k3_xboole_0(A_29, C_31))=k3_xboole_0(A_29, k4_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.31/2.03  tff(c_419, plain, (![A_43, B_44, C_45]: (k3_xboole_0(A_43, k4_xboole_0(B_44, k3_xboole_0(A_43, C_45)))=k3_xboole_0(A_43, k4_xboole_0(B_44, C_45)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_152])).
% 5.31/2.03  tff(c_447, plain, (![A_43, B_44, C_45]: (k4_xboole_0(A_43, k4_xboole_0(B_44, k3_xboole_0(A_43, C_45)))=k4_xboole_0(A_43, k3_xboole_0(A_43, k4_xboole_0(B_44, C_45))))), inference(superposition, [status(thm), theory('equality')], [c_419, c_6])).
% 5.31/2.03  tff(c_486, plain, (![A_43, B_44, C_45]: (k4_xboole_0(A_43, k4_xboole_0(B_44, k3_xboole_0(A_43, C_45)))=k4_xboole_0(A_43, k4_xboole_0(B_44, C_45)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_447])).
% 5.31/2.03  tff(c_15, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.31/2.03  tff(c_24, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k3_xboole_0(A_9, k4_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_15])).
% 5.31/2.03  tff(c_183, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_24])).
% 5.31/2.03  tff(c_30, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.31/2.03  tff(c_36, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, k3_xboole_0(A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_8])).
% 5.31/2.03  tff(c_41, plain, (![A_19, B_20]: (k3_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36])).
% 5.31/2.03  tff(c_171, plain, (![A_11, B_12, C_31]: (k3_xboole_0(A_11, k4_xboole_0(B_12, k3_xboole_0(A_11, C_31)))=k3_xboole_0(A_11, k4_xboole_0(B_12, C_31)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_152])).
% 5.31/2.03  tff(c_100, plain, (![A_26, B_27, C_28]: (k4_xboole_0(k4_xboole_0(A_26, B_27), C_28)=k4_xboole_0(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.31/2.03  tff(c_136, plain, (![A_9, B_10, C_28]: (k4_xboole_0(A_9, k2_xboole_0(k4_xboole_0(A_9, B_10), C_28))=k4_xboole_0(k3_xboole_0(A_9, B_10), C_28))), inference(superposition, [status(thm), theory('equality')], [c_8, c_100])).
% 5.31/2.03  tff(c_150, plain, (![A_9, B_10, C_28]: (k4_xboole_0(A_9, k2_xboole_0(k4_xboole_0(A_9, B_10), C_28))=k3_xboole_0(A_9, k4_xboole_0(B_10, C_28)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 5.31/2.03  tff(c_4, plain, (![A_4, B_5, C_6]: (k4_xboole_0(k4_xboole_0(A_4, B_5), C_6)=k4_xboole_0(A_4, k2_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.31/2.03  tff(c_140, plain, (![A_26, B_27, B_10]: (k4_xboole_0(A_26, k2_xboole_0(B_27, k4_xboole_0(k4_xboole_0(A_26, B_27), B_10)))=k3_xboole_0(k4_xboole_0(A_26, B_27), B_10))), inference(superposition, [status(thm), theory('equality')], [c_8, c_100])).
% 5.31/2.03  tff(c_1659, plain, (![A_76, B_77, B_78]: (k4_xboole_0(A_76, k2_xboole_0(B_77, k4_xboole_0(A_76, k2_xboole_0(B_77, B_78))))=k3_xboole_0(k4_xboole_0(A_76, B_77), B_78))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_140])).
% 5.31/2.03  tff(c_1684, plain, (![A_76, B_10, B_78]: (k3_xboole_0(A_76, k4_xboole_0(B_10, k4_xboole_0(A_76, k2_xboole_0(k4_xboole_0(A_76, B_10), B_78))))=k3_xboole_0(k4_xboole_0(A_76, k4_xboole_0(A_76, B_10)), B_78))), inference(superposition, [status(thm), theory('equality')], [c_1659, c_150])).
% 5.31/2.03  tff(c_1757, plain, (![A_76, B_10, B_78]: (k3_xboole_0(k3_xboole_0(A_76, B_10), B_78)=k3_xboole_0(A_76, k3_xboole_0(B_10, B_78)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_171, c_150, c_8, c_1684])).
% 5.31/2.03  tff(c_64, plain, (![A_23, B_24, C_25]: (k4_xboole_0(k3_xboole_0(A_23, B_24), C_25)=k3_xboole_0(A_23, k4_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.31/2.03  tff(c_74, plain, (![A_23, B_24, C_25]: (k4_xboole_0(k3_xboole_0(A_23, B_24), k3_xboole_0(A_23, k4_xboole_0(B_24, C_25)))=k3_xboole_0(k3_xboole_0(A_23, B_24), C_25))), inference(superposition, [status(thm), theory('equality')], [c_64, c_8])).
% 5.31/2.03  tff(c_3672, plain, (![A_110, B_111, C_112]: (k4_xboole_0(k3_xboole_0(A_110, B_111), k3_xboole_0(A_110, k4_xboole_0(B_111, C_112)))=k3_xboole_0(A_110, k3_xboole_0(B_111, C_112)))), inference(demodulation, [status(thm), theory('equality')], [c_1757, c_74])).
% 5.31/2.03  tff(c_3823, plain, (![A_9, B_10]: (k4_xboole_0(k3_xboole_0(A_9, A_9), k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, k3_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_183, c_3672])).
% 5.31/2.03  tff(c_3904, plain, (![A_113, B_114]: (k4_xboole_0(k3_xboole_0(A_113, A_113), k4_xboole_0(A_113, B_114))=k3_xboole_0(A_113, B_114))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_3823])).
% 5.31/2.03  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(A_1, C_3))=k4_xboole_0(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.31/2.03  tff(c_338, plain, (![A_40, B_41, C_42]: (k4_xboole_0(A_40, k2_xboole_0(k4_xboole_0(A_40, B_41), C_42))=k3_xboole_0(A_40, k4_xboole_0(B_41, C_42)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 5.31/2.03  tff(c_379, plain, (![A_1, B_2, C_3]: (k4_xboole_0(A_1, k4_xboole_0(A_1, k3_xboole_0(B_2, C_3)))=k3_xboole_0(A_1, k4_xboole_0(B_2, k4_xboole_0(A_1, C_3))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_338])).
% 5.31/2.03  tff(c_784, plain, (![A_55, B_56, C_57]: (k3_xboole_0(A_55, k4_xboole_0(B_56, k4_xboole_0(A_55, C_57)))=k3_xboole_0(A_55, k3_xboole_0(B_56, C_57)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_379])).
% 5.31/2.03  tff(c_825, plain, (![A_55, B_56, C_57]: (k4_xboole_0(A_55, k4_xboole_0(B_56, k4_xboole_0(A_55, C_57)))=k4_xboole_0(A_55, k3_xboole_0(A_55, k3_xboole_0(B_56, C_57))))), inference(superposition, [status(thm), theory('equality')], [c_784, c_6])).
% 5.31/2.03  tff(c_889, plain, (![A_55, B_56, C_57]: (k4_xboole_0(A_55, k4_xboole_0(B_56, k4_xboole_0(A_55, C_57)))=k4_xboole_0(A_55, k3_xboole_0(B_56, C_57)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_825])).
% 5.31/2.03  tff(c_3928, plain, (![A_113, B_56, B_114]: (k4_xboole_0(k3_xboole_0(A_113, A_113), k4_xboole_0(B_56, k3_xboole_0(A_113, B_114)))=k4_xboole_0(k3_xboole_0(A_113, A_113), k3_xboole_0(B_56, k4_xboole_0(A_113, B_114))))), inference(superposition, [status(thm), theory('equality')], [c_3904, c_889])).
% 5.31/2.03  tff(c_4059, plain, (![A_113, B_56, B_114]: (k2_xboole_0(k4_xboole_0(A_113, B_56), k3_xboole_0(A_113, B_114))=k4_xboole_0(A_113, k4_xboole_0(B_56, B_114)))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_486, c_183, c_183, c_10, c_10, c_3928])).
% 5.31/2.03  tff(c_14, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.31/2.03  tff(c_4601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4059, c_14])).
% 5.31/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/2.03  
% 5.31/2.03  Inference rules
% 5.31/2.03  ----------------------
% 5.31/2.03  #Ref     : 0
% 5.31/2.03  #Sup     : 1094
% 5.31/2.03  #Fact    : 0
% 5.31/2.03  #Define  : 0
% 5.31/2.03  #Split   : 0
% 5.31/2.03  #Chain   : 0
% 5.31/2.03  #Close   : 0
% 5.31/2.03  
% 5.31/2.03  Ordering : KBO
% 5.31/2.03  
% 5.31/2.03  Simplification rules
% 5.31/2.03  ----------------------
% 5.31/2.03  #Subsume      : 0
% 5.31/2.03  #Demod        : 1869
% 5.31/2.03  #Tautology    : 432
% 5.31/2.03  #SimpNegUnit  : 0
% 5.31/2.03  #BackRed      : 6
% 5.31/2.03  
% 5.31/2.03  #Partial instantiations: 0
% 5.31/2.03  #Strategies tried      : 1
% 5.31/2.03  
% 5.31/2.03  Timing (in seconds)
% 5.31/2.03  ----------------------
% 5.31/2.03  Preprocessing        : 0.29
% 5.31/2.03  Parsing              : 0.15
% 5.31/2.03  CNF conversion       : 0.02
% 5.31/2.03  Main loop            : 0.97
% 5.31/2.03  Inferencing          : 0.31
% 5.31/2.03  Reduction            : 0.48
% 5.31/2.03  Demodulation         : 0.40
% 5.31/2.03  BG Simplification    : 0.05
% 5.31/2.03  Subsumption          : 0.09
% 5.31/2.03  Abstraction          : 0.09
% 5.31/2.03  MUC search           : 0.00
% 5.31/2.03  Cooper               : 0.00
% 5.31/2.03  Total                : 1.29
% 5.31/2.03  Index Insertion      : 0.00
% 5.31/2.03  Index Deletion       : 0.00
% 5.31/2.03  Index Matching       : 0.00
% 5.31/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
