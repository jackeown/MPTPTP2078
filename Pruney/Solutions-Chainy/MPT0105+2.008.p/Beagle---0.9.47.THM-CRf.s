%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:48 EST 2020

% Result     : Theorem 5.00s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 107 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :   45 (  97 expanded)
%              Number of equality atoms :   44 (  96 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_187,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_205,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_187])).

tff(c_215,plain,(
    ! [A_39,B_40] : k3_xboole_0(A_39,k2_xboole_0(A_39,B_40)) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_205])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_221,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_14])).

tff(c_226,plain,(
    ! [A_39] : k4_xboole_0(A_39,A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_221])).

tff(c_208,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_187])).

tff(c_315,plain,(
    ! [A_45] : k3_xboole_0(A_45,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_208])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_350,plain,(
    ! [A_46] : k3_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_2])).

tff(c_366,plain,(
    ! [A_46] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_14])).

tff(c_493,plain,(
    ! [A_50] : k4_xboole_0(k1_xboole_0,A_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_366])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k4_xboole_0(A_5,B_6),k4_xboole_0(B_6,A_5)) = k5_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_501,plain,(
    ! [A_50] : k2_xboole_0(k4_xboole_0(A_50,k1_xboole_0),k1_xboole_0) = k5_xboole_0(A_50,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_6])).

tff(c_545,plain,(
    ! [A_50] : k2_xboole_0(A_50,k1_xboole_0) = A_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20,c_501])).

tff(c_314,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_208])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_172,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1420,plain,(
    ! [B_75,A_76] : k4_xboole_0(B_75,k3_xboole_0(A_76,B_75)) = k4_xboole_0(B_75,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_172])).

tff(c_1447,plain,(
    ! [B_75,A_76] : k2_xboole_0(k4_xboole_0(B_75,A_76),k4_xboole_0(k3_xboole_0(A_76,B_75),B_75)) = k5_xboole_0(B_75,k3_xboole_0(A_76,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_6])).

tff(c_1505,plain,(
    ! [B_75,A_76] : k5_xboole_0(B_75,k3_xboole_0(A_76,B_75)) = k4_xboole_0(B_75,A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_314,c_226,c_18,c_1447])).

tff(c_576,plain,(
    ! [A_52,B_53,C_54] : k5_xboole_0(k5_xboole_0(A_52,B_53),C_54) = k5_xboole_0(A_52,k5_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6594,plain,(
    ! [C_156,A_157,B_158] : k5_xboole_0(C_156,k5_xboole_0(A_157,B_158)) = k5_xboole_0(A_157,k5_xboole_0(B_158,C_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_4])).

tff(c_660,plain,(
    ! [A_56,B_57] : k5_xboole_0(k5_xboole_0(A_56,B_57),k3_xboole_0(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_675,plain,(
    ! [A_56,B_57] : k5_xboole_0(k3_xboole_0(A_56,B_57),k5_xboole_0(A_56,B_57)) = k2_xboole_0(A_56,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_4])).

tff(c_6650,plain,(
    ! [A_157,B_158] : k5_xboole_0(A_157,k5_xboole_0(B_158,k3_xboole_0(A_157,B_158))) = k2_xboole_0(A_157,B_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_6594,c_675])).

tff(c_6978,plain,(
    ! [A_157,B_158] : k5_xboole_0(A_157,k4_xboole_0(B_158,A_157)) = k2_xboole_0(A_157,B_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1505,c_6650])).

tff(c_26,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_7437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6978,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.00/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/2.19  
% 5.00/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/2.19  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 5.00/2.19  
% 5.00/2.19  %Foreground sorts:
% 5.00/2.19  
% 5.00/2.19  
% 5.00/2.19  %Background operators:
% 5.00/2.19  
% 5.00/2.19  
% 5.00/2.19  %Foreground operators:
% 5.00/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.00/2.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.00/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.00/2.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.00/2.19  tff('#skF_2', type, '#skF_2': $i).
% 5.00/2.19  tff('#skF_1', type, '#skF_1': $i).
% 5.00/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.00/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.00/2.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.00/2.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.00/2.19  
% 5.00/2.20  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.00/2.20  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.00/2.20  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.00/2.20  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.00/2.20  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.00/2.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.00/2.20  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.00/2.20  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.00/2.20  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.00/2.20  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.00/2.20  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.00/2.20  tff(f_52, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.00/2.20  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.00/2.20  tff(c_20, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.00/2.20  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.00/2.20  tff(c_187, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.00/2.20  tff(c_205, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_187])).
% 5.00/2.20  tff(c_215, plain, (![A_39, B_40]: (k3_xboole_0(A_39, k2_xboole_0(A_39, B_40))=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_205])).
% 5.00/2.20  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.00/2.20  tff(c_221, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(A_39, B_40))=k4_xboole_0(A_39, A_39))), inference(superposition, [status(thm), theory('equality')], [c_215, c_14])).
% 5.00/2.20  tff(c_226, plain, (![A_39]: (k4_xboole_0(A_39, A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_221])).
% 5.00/2.20  tff(c_208, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_187])).
% 5.00/2.20  tff(c_315, plain, (![A_45]: (k3_xboole_0(A_45, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_226, c_208])).
% 5.00/2.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.00/2.20  tff(c_350, plain, (![A_46]: (k3_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_315, c_2])).
% 5.00/2.20  tff(c_366, plain, (![A_46]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_46))), inference(superposition, [status(thm), theory('equality')], [c_350, c_14])).
% 5.00/2.20  tff(c_493, plain, (![A_50]: (k4_xboole_0(k1_xboole_0, A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_366])).
% 5.00/2.20  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k4_xboole_0(A_5, B_6), k4_xboole_0(B_6, A_5))=k5_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.00/2.20  tff(c_501, plain, (![A_50]: (k2_xboole_0(k4_xboole_0(A_50, k1_xboole_0), k1_xboole_0)=k5_xboole_0(A_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_493, c_6])).
% 5.00/2.20  tff(c_545, plain, (![A_50]: (k2_xboole_0(A_50, k1_xboole_0)=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20, c_501])).
% 5.00/2.20  tff(c_314, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_226, c_208])).
% 5.00/2.20  tff(c_18, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), C_19)=k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.00/2.20  tff(c_172, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.00/2.20  tff(c_1420, plain, (![B_75, A_76]: (k4_xboole_0(B_75, k3_xboole_0(A_76, B_75))=k4_xboole_0(B_75, A_76))), inference(superposition, [status(thm), theory('equality')], [c_2, c_172])).
% 5.00/2.20  tff(c_1447, plain, (![B_75, A_76]: (k2_xboole_0(k4_xboole_0(B_75, A_76), k4_xboole_0(k3_xboole_0(A_76, B_75), B_75))=k5_xboole_0(B_75, k3_xboole_0(A_76, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_6])).
% 5.00/2.20  tff(c_1505, plain, (![B_75, A_76]: (k5_xboole_0(B_75, k3_xboole_0(A_76, B_75))=k4_xboole_0(B_75, A_76))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_314, c_226, c_18, c_1447])).
% 5.00/2.20  tff(c_576, plain, (![A_52, B_53, C_54]: (k5_xboole_0(k5_xboole_0(A_52, B_53), C_54)=k5_xboole_0(A_52, k5_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.00/2.20  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.00/2.20  tff(c_6594, plain, (![C_156, A_157, B_158]: (k5_xboole_0(C_156, k5_xboole_0(A_157, B_158))=k5_xboole_0(A_157, k5_xboole_0(B_158, C_156)))), inference(superposition, [status(thm), theory('equality')], [c_576, c_4])).
% 5.00/2.20  tff(c_660, plain, (![A_56, B_57]: (k5_xboole_0(k5_xboole_0(A_56, B_57), k3_xboole_0(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.00/2.20  tff(c_675, plain, (![A_56, B_57]: (k5_xboole_0(k3_xboole_0(A_56, B_57), k5_xboole_0(A_56, B_57))=k2_xboole_0(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_660, c_4])).
% 5.00/2.20  tff(c_6650, plain, (![A_157, B_158]: (k5_xboole_0(A_157, k5_xboole_0(B_158, k3_xboole_0(A_157, B_158)))=k2_xboole_0(A_157, B_158))), inference(superposition, [status(thm), theory('equality')], [c_6594, c_675])).
% 5.00/2.20  tff(c_6978, plain, (![A_157, B_158]: (k5_xboole_0(A_157, k4_xboole_0(B_158, A_157))=k2_xboole_0(A_157, B_158))), inference(demodulation, [status(thm), theory('equality')], [c_1505, c_6650])).
% 5.00/2.20  tff(c_26, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.00/2.20  tff(c_7437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6978, c_26])).
% 5.00/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.00/2.20  
% 5.00/2.20  Inference rules
% 5.00/2.20  ----------------------
% 5.00/2.20  #Ref     : 0
% 5.00/2.20  #Sup     : 1869
% 5.00/2.20  #Fact    : 0
% 5.00/2.20  #Define  : 0
% 5.00/2.20  #Split   : 0
% 5.00/2.20  #Chain   : 0
% 5.00/2.20  #Close   : 0
% 5.00/2.20  
% 5.00/2.20  Ordering : KBO
% 5.00/2.20  
% 5.00/2.20  Simplification rules
% 5.00/2.20  ----------------------
% 5.00/2.20  #Subsume      : 27
% 5.00/2.20  #Demod        : 1680
% 5.00/2.20  #Tautology    : 1187
% 5.00/2.20  #SimpNegUnit  : 0
% 5.00/2.20  #BackRed      : 1
% 5.00/2.20  
% 5.00/2.20  #Partial instantiations: 0
% 5.00/2.20  #Strategies tried      : 1
% 5.00/2.20  
% 5.00/2.20  Timing (in seconds)
% 5.00/2.20  ----------------------
% 5.26/2.21  Preprocessing        : 0.28
% 5.26/2.21  Parsing              : 0.15
% 5.26/2.21  CNF conversion       : 0.01
% 5.26/2.21  Main loop            : 1.12
% 5.26/2.21  Inferencing          : 0.31
% 5.26/2.21  Reduction            : 0.56
% 5.26/2.21  Demodulation         : 0.48
% 5.26/2.21  BG Simplification    : 0.04
% 5.26/2.21  Subsumption          : 0.16
% 5.26/2.21  Abstraction          : 0.06
% 5.26/2.21  MUC search           : 0.00
% 5.26/2.21  Cooper               : 0.00
% 5.26/2.21  Total                : 1.44
% 5.26/2.21  Index Insertion      : 0.00
% 5.26/2.21  Index Deletion       : 0.00
% 5.26/2.21  Index Matching       : 0.00
% 5.26/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
