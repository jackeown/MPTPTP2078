%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:44 EST 2020

% Result     : Theorem 4.39s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   59 (  97 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   49 (  87 expanded)
%              Number of equality atoms :   48 (  86 expanded)
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

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_256,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_259,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,k4_xboole_0(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_20])).

tff(c_1434,plain,(
    ! [A_79,B_80] : k3_xboole_0(A_79,k4_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_259])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_503,plain,(
    ! [A_49,B_50] : k4_xboole_0(k2_xboole_0(A_49,B_50),k3_xboole_0(A_49,B_50)) = k5_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_539,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,k3_xboole_0(A_8,B_9))) = k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_503])).

tff(c_550,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_539])).

tff(c_1443,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k4_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,k4_xboole_0(A_79,B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1434,c_550])).

tff(c_1508,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k4_xboole_0(A_79,B_80)) = k3_xboole_0(A_79,B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1443])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_30] : k2_xboole_0(k1_xboole_0,A_30) = A_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_8])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [A_31] : k2_xboole_0(k1_xboole_0,A_31) = A_31 ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_8])).

tff(c_134,plain,(
    ! [B_9] : k3_xboole_0(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_102])).

tff(c_215,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_224,plain,(
    ! [B_9] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_215])).

tff(c_227,plain,(
    ! [B_9] : k4_xboole_0(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_224])).

tff(c_147,plain,(
    ! [A_32,B_33] : k4_xboole_0(k2_xboole_0(A_32,B_33),B_33) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_160,plain,(
    ! [A_30] : k4_xboole_0(k1_xboole_0,A_30) = k4_xboole_0(A_30,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_147])).

tff(c_228,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_160])).

tff(c_808,plain,(
    ! [A_60,B_61,C_62] : k4_xboole_0(k4_xboole_0(A_60,B_61),C_62) = k4_xboole_0(A_60,k2_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_851,plain,(
    ! [A_30,C_62] : k4_xboole_0(A_30,k2_xboole_0(A_30,C_62)) = k4_xboole_0(k1_xboole_0,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_808])).

tff(c_890,plain,(
    ! [A_30,C_62] : k4_xboole_0(A_30,k2_xboole_0(A_30,C_62)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_851])).

tff(c_1175,plain,(
    ! [B_71,A_72] : k4_xboole_0(k2_xboole_0(B_71,A_72),B_71) = k4_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1187,plain,(
    ! [B_71,A_72] : k2_xboole_0(k4_xboole_0(B_71,k2_xboole_0(B_71,A_72)),k4_xboole_0(A_72,B_71)) = k5_xboole_0(B_71,k2_xboole_0(B_71,A_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_4])).

tff(c_3103,plain,(
    ! [B_110,A_111] : k5_xboole_0(B_110,k2_xboole_0(B_110,A_111)) = k4_xboole_0(A_111,B_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_890,c_1187])).

tff(c_3167,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3103])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] : k5_xboole_0(k5_xboole_0(A_20,B_21),C_22) = k5_xboole_0(A_20,k5_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_2'))) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_5771,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3167,c_27])).

tff(c_5774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1508,c_5771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:08:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.39/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.87  
% 4.39/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.88  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.39/1.88  
% 4.39/1.88  %Foreground sorts:
% 4.39/1.88  
% 4.39/1.88  
% 4.39/1.88  %Background operators:
% 4.39/1.88  
% 4.39/1.88  
% 4.39/1.88  %Foreground operators:
% 4.39/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.39/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.39/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.39/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.39/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.39/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.39/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.39/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.39/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.39/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.39/1.88  
% 4.39/1.89  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.39/1.89  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.39/1.89  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.39/1.89  tff(f_31, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 4.39/1.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.39/1.89  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.39/1.89  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.39/1.89  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.39/1.89  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.39/1.89  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.39/1.89  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.39/1.89  tff(f_52, negated_conjecture, ~(![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.39/1.89  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.39/1.89  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.39/1.89  tff(c_256, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.39/1.89  tff(c_259, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k3_xboole_0(A_39, k4_xboole_0(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_256, c_20])).
% 4.39/1.89  tff(c_1434, plain, (![A_79, B_80]: (k3_xboole_0(A_79, k4_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_259])).
% 4.39/1.89  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.39/1.89  tff(c_503, plain, (![A_49, B_50]: (k4_xboole_0(k2_xboole_0(A_49, B_50), k3_xboole_0(A_49, B_50))=k5_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.39/1.89  tff(c_539, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, k3_xboole_0(A_8, B_9)))=k5_xboole_0(A_8, k3_xboole_0(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_503])).
% 4.39/1.89  tff(c_550, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_539])).
% 4.39/1.89  tff(c_1443, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k4_xboole_0(A_79, B_80))=k4_xboole_0(A_79, k4_xboole_0(A_79, B_80)))), inference(superposition, [status(thm), theory('equality')], [c_1434, c_550])).
% 4.39/1.89  tff(c_1508, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k4_xboole_0(A_79, B_80))=k3_xboole_0(A_79, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1443])).
% 4.39/1.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.39/1.89  tff(c_55, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.39/1.89  tff(c_8, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.39/1.89  tff(c_71, plain, (![A_30]: (k2_xboole_0(k1_xboole_0, A_30)=A_30)), inference(superposition, [status(thm), theory('equality')], [c_55, c_8])).
% 4.39/1.89  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.39/1.89  tff(c_102, plain, (![A_31]: (k2_xboole_0(k1_xboole_0, A_31)=A_31)), inference(superposition, [status(thm), theory('equality')], [c_55, c_8])).
% 4.39/1.89  tff(c_134, plain, (![B_9]: (k3_xboole_0(k1_xboole_0, B_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_102])).
% 4.39/1.89  tff(c_215, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.39/1.89  tff(c_224, plain, (![B_9]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_9))), inference(superposition, [status(thm), theory('equality')], [c_134, c_215])).
% 4.39/1.89  tff(c_227, plain, (![B_9]: (k4_xboole_0(k1_xboole_0, B_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_224])).
% 4.39/1.89  tff(c_147, plain, (![A_32, B_33]: (k4_xboole_0(k2_xboole_0(A_32, B_33), B_33)=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.39/1.89  tff(c_160, plain, (![A_30]: (k4_xboole_0(k1_xboole_0, A_30)=k4_xboole_0(A_30, A_30))), inference(superposition, [status(thm), theory('equality')], [c_71, c_147])).
% 4.39/1.89  tff(c_228, plain, (![A_30]: (k4_xboole_0(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_227, c_160])).
% 4.39/1.89  tff(c_808, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k4_xboole_0(A_60, B_61), C_62)=k4_xboole_0(A_60, k2_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.39/1.89  tff(c_851, plain, (![A_30, C_62]: (k4_xboole_0(A_30, k2_xboole_0(A_30, C_62))=k4_xboole_0(k1_xboole_0, C_62))), inference(superposition, [status(thm), theory('equality')], [c_228, c_808])).
% 4.39/1.89  tff(c_890, plain, (![A_30, C_62]: (k4_xboole_0(A_30, k2_xboole_0(A_30, C_62))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_227, c_851])).
% 4.39/1.89  tff(c_1175, plain, (![B_71, A_72]: (k4_xboole_0(k2_xboole_0(B_71, A_72), B_71)=k4_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_2, c_147])).
% 4.39/1.89  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.39/1.89  tff(c_1187, plain, (![B_71, A_72]: (k2_xboole_0(k4_xboole_0(B_71, k2_xboole_0(B_71, A_72)), k4_xboole_0(A_72, B_71))=k5_xboole_0(B_71, k2_xboole_0(B_71, A_72)))), inference(superposition, [status(thm), theory('equality')], [c_1175, c_4])).
% 4.39/1.89  tff(c_3103, plain, (![B_110, A_111]: (k5_xboole_0(B_110, k2_xboole_0(B_110, A_111))=k4_xboole_0(A_111, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_890, c_1187])).
% 4.39/1.89  tff(c_3167, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3103])).
% 4.39/1.89  tff(c_22, plain, (![A_20, B_21, C_22]: (k5_xboole_0(k5_xboole_0(A_20, B_21), C_22)=k5_xboole_0(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.39/1.89  tff(c_26, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.39/1.89  tff(c_27, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_2')))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 4.39/1.89  tff(c_5771, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3167, c_27])).
% 4.39/1.89  tff(c_5774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1508, c_5771])).
% 4.39/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.89  
% 4.39/1.89  Inference rules
% 4.39/1.89  ----------------------
% 4.39/1.89  #Ref     : 0
% 4.39/1.89  #Sup     : 1456
% 4.39/1.89  #Fact    : 0
% 4.39/1.89  #Define  : 0
% 4.39/1.89  #Split   : 0
% 4.39/1.89  #Chain   : 0
% 4.39/1.89  #Close   : 0
% 4.39/1.89  
% 4.39/1.89  Ordering : KBO
% 4.39/1.89  
% 4.39/1.89  Simplification rules
% 4.39/1.89  ----------------------
% 4.39/1.89  #Subsume      : 5
% 4.39/1.89  #Demod        : 1453
% 4.39/1.89  #Tautology    : 942
% 4.39/1.89  #SimpNegUnit  : 0
% 4.39/1.89  #BackRed      : 3
% 4.39/1.89  
% 4.39/1.89  #Partial instantiations: 0
% 4.39/1.89  #Strategies tried      : 1
% 4.39/1.89  
% 4.39/1.89  Timing (in seconds)
% 4.39/1.89  ----------------------
% 4.39/1.89  Preprocessing        : 0.27
% 4.39/1.89  Parsing              : 0.15
% 4.39/1.89  CNF conversion       : 0.01
% 4.39/1.89  Main loop            : 0.86
% 4.39/1.89  Inferencing          : 0.26
% 4.39/1.89  Reduction            : 0.40
% 4.39/1.89  Demodulation         : 0.34
% 4.39/1.89  BG Simplification    : 0.03
% 4.39/1.89  Subsumption          : 0.11
% 4.39/1.89  Abstraction          : 0.05
% 4.39/1.89  MUC search           : 0.00
% 4.39/1.89  Cooper               : 0.00
% 4.39/1.89  Total                : 1.16
% 4.39/1.89  Index Insertion      : 0.00
% 4.39/1.89  Index Deletion       : 0.00
% 4.39/1.89  Index Matching       : 0.00
% 4.39/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
