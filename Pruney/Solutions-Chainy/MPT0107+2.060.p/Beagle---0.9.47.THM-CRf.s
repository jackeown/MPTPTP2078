%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:00 EST 2020

% Result     : Theorem 8.13s
% Output     : CNFRefutation 8.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 111 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   18
%              Number of atoms          :   44 ( 101 expanded)
%              Number of equality atoms :   43 ( 100 expanded)
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

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,k4_xboole_0(A_23,B_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_12])).

tff(c_820,plain,(
    ! [A_23,B_24] : k3_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k3_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_87])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_105,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_111,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_105])).

tff(c_162,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_180,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_162])).

tff(c_185,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_8,c_180])).

tff(c_199,plain,(
    ! [A_31] : k4_xboole_0(A_31,A_31) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_108])).

tff(c_207,plain,(
    ! [A_31] : k5_xboole_0(A_31,k1_xboole_0) = k2_xboole_0(A_31,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_16])).

tff(c_220,plain,(
    ! [A_31] : k2_xboole_0(A_31,A_31) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_207])).

tff(c_224,plain,(
    ! [A_32,B_33,C_34] : k4_xboole_0(k4_xboole_0(A_32,B_33),C_34) = k4_xboole_0(A_32,k2_xboole_0(B_33,C_34)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6943,plain,(
    ! [C_141,A_142,B_143] : k5_xboole_0(C_141,k4_xboole_0(A_142,k2_xboole_0(B_143,C_141))) = k2_xboole_0(C_141,k4_xboole_0(A_142,B_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_16])).

tff(c_7046,plain,(
    ! [A_31,A_142] : k5_xboole_0(A_31,k4_xboole_0(A_142,A_31)) = k2_xboole_0(A_31,k4_xboole_0(A_142,A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_6943])).

tff(c_7090,plain,(
    ! [A_31,A_142] : k2_xboole_0(A_31,k4_xboole_0(A_142,A_31)) = k2_xboole_0(A_31,A_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_7046])).

tff(c_186,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_108])).

tff(c_234,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k2_xboole_0(B_33,k4_xboole_0(A_32,B_33))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_186])).

tff(c_8185,plain,(
    ! [A_152,B_153] : k4_xboole_0(A_152,k2_xboole_0(B_153,A_152)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7090,c_234])).

tff(c_248,plain,(
    ! [C_34,A_32,B_33] : k5_xboole_0(C_34,k4_xboole_0(A_32,k2_xboole_0(B_33,C_34))) = k2_xboole_0(C_34,k4_xboole_0(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_16])).

tff(c_8196,plain,(
    ! [A_152,B_153] : k2_xboole_0(A_152,k4_xboole_0(A_152,B_153)) = k5_xboole_0(A_152,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8185,c_248])).

tff(c_8397,plain,(
    ! [A_154,B_155] : k2_xboole_0(A_154,k4_xboole_0(A_154,B_155)) = A_154 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8196])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8587,plain,(
    ! [A_154,B_155] : k4_xboole_0(A_154,k3_xboole_0(A_154,k4_xboole_0(A_154,B_155))) = k5_xboole_0(A_154,k4_xboole_0(A_154,B_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8397,c_2])).

tff(c_20458,plain,(
    ! [A_255,B_256] : k5_xboole_0(A_255,k4_xboole_0(A_255,B_256)) = k3_xboole_0(A_255,B_256) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_8587])).

tff(c_20618,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_20458])).

tff(c_20679,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_20618])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_23644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20679,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:53:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.13/3.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.13/3.24  
% 8.13/3.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.13/3.24  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 8.13/3.24  
% 8.13/3.24  %Foreground sorts:
% 8.13/3.24  
% 8.13/3.24  
% 8.13/3.24  %Background operators:
% 8.13/3.24  
% 8.13/3.24  
% 8.13/3.24  %Foreground operators:
% 8.13/3.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.13/3.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.13/3.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.13/3.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.13/3.24  tff('#skF_2', type, '#skF_2': $i).
% 8.13/3.24  tff('#skF_1', type, '#skF_1': $i).
% 8.13/3.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.13/3.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.13/3.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.13/3.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.13/3.24  
% 8.13/3.25  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.13/3.25  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.13/3.25  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.13/3.25  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.13/3.25  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.13/3.25  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.13/3.25  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.13/3.26  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 8.13/3.26  tff(f_44, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.13/3.26  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.13/3.26  tff(c_87, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.13/3.26  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.13/3.26  tff(c_90, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k3_xboole_0(A_23, k4_xboole_0(A_23, B_24)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_12])).
% 8.13/3.26  tff(c_820, plain, (![A_23, B_24]: (k3_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_90])).
% 8.13/3.26  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.13/3.26  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.13/3.26  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.13/3.26  tff(c_108, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k3_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_87])).
% 8.13/3.26  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.13/3.26  tff(c_105, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_87])).
% 8.13/3.26  tff(c_111, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_105])).
% 8.13/3.26  tff(c_162, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.13/3.26  tff(c_180, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_111, c_162])).
% 8.13/3.26  tff(c_185, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_8, c_180])).
% 8.13/3.26  tff(c_199, plain, (![A_31]: (k4_xboole_0(A_31, A_31)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_185, c_108])).
% 8.13/3.26  tff(c_207, plain, (![A_31]: (k5_xboole_0(A_31, k1_xboole_0)=k2_xboole_0(A_31, A_31))), inference(superposition, [status(thm), theory('equality')], [c_199, c_16])).
% 8.13/3.26  tff(c_220, plain, (![A_31]: (k2_xboole_0(A_31, A_31)=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_207])).
% 8.13/3.26  tff(c_224, plain, (![A_32, B_33, C_34]: (k4_xboole_0(k4_xboole_0(A_32, B_33), C_34)=k4_xboole_0(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.13/3.26  tff(c_6943, plain, (![C_141, A_142, B_143]: (k5_xboole_0(C_141, k4_xboole_0(A_142, k2_xboole_0(B_143, C_141)))=k2_xboole_0(C_141, k4_xboole_0(A_142, B_143)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_16])).
% 8.13/3.26  tff(c_7046, plain, (![A_31, A_142]: (k5_xboole_0(A_31, k4_xboole_0(A_142, A_31))=k2_xboole_0(A_31, k4_xboole_0(A_142, A_31)))), inference(superposition, [status(thm), theory('equality')], [c_220, c_6943])).
% 8.13/3.26  tff(c_7090, plain, (![A_31, A_142]: (k2_xboole_0(A_31, k4_xboole_0(A_142, A_31))=k2_xboole_0(A_31, A_142))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_7046])).
% 8.13/3.26  tff(c_186, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_185, c_108])).
% 8.13/3.26  tff(c_234, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k2_xboole_0(B_33, k4_xboole_0(A_32, B_33)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_224, c_186])).
% 8.13/3.26  tff(c_8185, plain, (![A_152, B_153]: (k4_xboole_0(A_152, k2_xboole_0(B_153, A_152))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7090, c_234])).
% 8.13/3.26  tff(c_248, plain, (![C_34, A_32, B_33]: (k5_xboole_0(C_34, k4_xboole_0(A_32, k2_xboole_0(B_33, C_34)))=k2_xboole_0(C_34, k4_xboole_0(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_16])).
% 8.13/3.26  tff(c_8196, plain, (![A_152, B_153]: (k2_xboole_0(A_152, k4_xboole_0(A_152, B_153))=k5_xboole_0(A_152, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8185, c_248])).
% 8.13/3.26  tff(c_8397, plain, (![A_154, B_155]: (k2_xboole_0(A_154, k4_xboole_0(A_154, B_155))=A_154)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_8196])).
% 8.13/3.26  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.13/3.26  tff(c_8587, plain, (![A_154, B_155]: (k4_xboole_0(A_154, k3_xboole_0(A_154, k4_xboole_0(A_154, B_155)))=k5_xboole_0(A_154, k4_xboole_0(A_154, B_155)))), inference(superposition, [status(thm), theory('equality')], [c_8397, c_2])).
% 8.13/3.26  tff(c_20458, plain, (![A_255, B_256]: (k5_xboole_0(A_255, k4_xboole_0(A_255, B_256))=k3_xboole_0(A_255, B_256))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_8587])).
% 8.13/3.26  tff(c_20618, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k3_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_20458])).
% 8.13/3.26  tff(c_20679, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_820, c_20618])).
% 8.13/3.26  tff(c_18, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.13/3.26  tff(c_23644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20679, c_18])).
% 8.13/3.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.13/3.26  
% 8.13/3.26  Inference rules
% 8.13/3.26  ----------------------
% 8.13/3.26  #Ref     : 0
% 8.13/3.26  #Sup     : 5797
% 8.13/3.26  #Fact    : 0
% 8.13/3.26  #Define  : 0
% 8.13/3.26  #Split   : 0
% 8.13/3.26  #Chain   : 0
% 8.13/3.26  #Close   : 0
% 8.13/3.26  
% 8.13/3.26  Ordering : KBO
% 8.13/3.26  
% 8.13/3.26  Simplification rules
% 8.13/3.26  ----------------------
% 8.13/3.26  #Subsume      : 0
% 8.13/3.26  #Demod        : 7248
% 8.13/3.26  #Tautology    : 4214
% 8.13/3.26  #SimpNegUnit  : 0
% 8.13/3.26  #BackRed      : 6
% 8.13/3.26  
% 8.13/3.26  #Partial instantiations: 0
% 8.13/3.26  #Strategies tried      : 1
% 8.13/3.26  
% 8.13/3.26  Timing (in seconds)
% 8.13/3.26  ----------------------
% 8.13/3.26  Preprocessing        : 0.29
% 8.13/3.26  Parsing              : 0.16
% 8.13/3.26  CNF conversion       : 0.02
% 8.13/3.26  Main loop            : 2.20
% 8.13/3.26  Inferencing          : 0.58
% 8.13/3.26  Reduction            : 1.15
% 8.13/3.26  Demodulation         : 1.01
% 8.13/3.26  BG Simplification    : 0.06
% 8.13/3.26  Subsumption          : 0.30
% 8.13/3.26  Abstraction          : 0.13
% 8.13/3.26  MUC search           : 0.00
% 8.13/3.26  Cooper               : 0.00
% 8.13/3.26  Total                : 2.51
% 8.13/3.26  Index Insertion      : 0.00
% 8.13/3.26  Index Deletion       : 0.00
% 8.13/3.26  Index Matching       : 0.00
% 8.13/3.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
