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
% DateTime   : Thu Dec  3 09:45:06 EST 2020

% Result     : Theorem 42.23s
% Output     : CNFRefutation 42.26s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   28 (  39 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    5 (   3 average)

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k4_xboole_0(k3_xboole_0(A_12,B_13),C_14) = k3_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_370,plain,(
    ! [A_41,B_42] : k5_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_394,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_370])).

tff(c_477,plain,(
    ! [A_46,B_47,C_48] : k5_xboole_0(k5_xboole_0(A_46,B_47),C_48) = k5_xboole_0(A_46,k5_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5988,plain,(
    ! [A_150,B_151,C_152] : k5_xboole_0(A_150,k5_xboole_0(k3_xboole_0(A_150,B_151),C_152)) = k5_xboole_0(k4_xboole_0(A_150,B_151),C_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_477])).

tff(c_6119,plain,(
    ! [A_150,B_151,A_1] : k5_xboole_0(k4_xboole_0(A_150,B_151),k3_xboole_0(A_1,k3_xboole_0(A_150,B_151))) = k5_xboole_0(A_150,k4_xboole_0(k3_xboole_0(A_150,B_151),A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_5988])).

tff(c_6179,plain,(
    ! [A_150,B_151,A_1] : k5_xboole_0(k4_xboole_0(A_150,B_151),k3_xboole_0(A_1,k3_xboole_0(A_150,B_151))) = k4_xboole_0(A_150,k4_xboole_0(B_151,A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14,c_6119])).

tff(c_18,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8492,plain,(
    ! [A_183,B_184,B_185] : k5_xboole_0(A_183,k5_xboole_0(B_184,k3_xboole_0(k5_xboole_0(A_183,B_184),B_185))) = k4_xboole_0(k5_xboole_0(A_183,B_184),B_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_4])).

tff(c_8694,plain,(
    ! [A_18,B_19,B_185] : k5_xboole_0(A_18,k5_xboole_0(k4_xboole_0(B_19,A_18),k3_xboole_0(k2_xboole_0(A_18,B_19),B_185))) = k4_xboole_0(k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)),B_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_8492])).

tff(c_84834,plain,(
    ! [A_598,B_599,B_600] : k5_xboole_0(A_598,k5_xboole_0(k4_xboole_0(B_599,A_598),k3_xboole_0(k2_xboole_0(A_598,B_599),B_600))) = k4_xboole_0(k2_xboole_0(A_598,B_599),B_600) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8694])).

tff(c_85018,plain,(
    ! [B_151,A_150] : k5_xboole_0(B_151,k4_xboole_0(A_150,k4_xboole_0(B_151,k2_xboole_0(B_151,A_150)))) = k4_xboole_0(k2_xboole_0(B_151,A_150),k3_xboole_0(A_150,B_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6179,c_84834])).

tff(c_86250,plain,(
    ! [B_604,A_605] : k4_xboole_0(k2_xboole_0(B_604,A_605),k3_xboole_0(A_605,B_604)) = k5_xboole_0(B_604,A_605) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_85018])).

tff(c_86832,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k3_xboole_0(A_1,B_2)) = k5_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86250])).

tff(c_20,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_2')) != k5_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_158026,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86832,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:00 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 42.23/33.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.23/33.91  
% 42.23/33.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.23/33.91  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 42.23/33.91  
% 42.23/33.91  %Foreground sorts:
% 42.23/33.91  
% 42.23/33.91  
% 42.23/33.91  %Background operators:
% 42.23/33.91  
% 42.23/33.91  
% 42.23/33.91  %Foreground operators:
% 42.23/33.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 42.23/33.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 42.23/33.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 42.23/33.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 42.23/33.91  tff('#skF_2', type, '#skF_2': $i).
% 42.23/33.91  tff('#skF_1', type, '#skF_1': $i).
% 42.23/33.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 42.23/33.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 42.23/33.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 42.23/33.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 42.26/33.91  
% 42.26/33.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 42.26/33.92  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 42.26/33.92  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 42.26/33.92  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 42.26/33.92  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 42.26/33.92  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 42.26/33.92  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 42.26/33.92  tff(f_46, negated_conjecture, ~(![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_xboole_1)).
% 42.26/33.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 42.26/33.92  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 42.26/33.92  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 42.26/33.92  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 42.26/33.92  tff(c_14, plain, (![A_12, B_13, C_14]: (k4_xboole_0(k3_xboole_0(A_12, B_13), C_14)=k3_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 42.26/33.92  tff(c_370, plain, (![A_41, B_42]: (k5_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 42.26/33.92  tff(c_394, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_370])).
% 42.26/33.92  tff(c_477, plain, (![A_46, B_47, C_48]: (k5_xboole_0(k5_xboole_0(A_46, B_47), C_48)=k5_xboole_0(A_46, k5_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 42.26/33.92  tff(c_5988, plain, (![A_150, B_151, C_152]: (k5_xboole_0(A_150, k5_xboole_0(k3_xboole_0(A_150, B_151), C_152))=k5_xboole_0(k4_xboole_0(A_150, B_151), C_152))), inference(superposition, [status(thm), theory('equality')], [c_4, c_477])).
% 42.26/33.92  tff(c_6119, plain, (![A_150, B_151, A_1]: (k5_xboole_0(k4_xboole_0(A_150, B_151), k3_xboole_0(A_1, k3_xboole_0(A_150, B_151)))=k5_xboole_0(A_150, k4_xboole_0(k3_xboole_0(A_150, B_151), A_1)))), inference(superposition, [status(thm), theory('equality')], [c_394, c_5988])).
% 42.26/33.92  tff(c_6179, plain, (![A_150, B_151, A_1]: (k5_xboole_0(k4_xboole_0(A_150, B_151), k3_xboole_0(A_1, k3_xboole_0(A_150, B_151)))=k4_xboole_0(A_150, k4_xboole_0(B_151, A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14, c_6119])).
% 42.26/33.92  tff(c_18, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 42.26/33.92  tff(c_8492, plain, (![A_183, B_184, B_185]: (k5_xboole_0(A_183, k5_xboole_0(B_184, k3_xboole_0(k5_xboole_0(A_183, B_184), B_185)))=k4_xboole_0(k5_xboole_0(A_183, B_184), B_185))), inference(superposition, [status(thm), theory('equality')], [c_477, c_4])).
% 42.26/33.92  tff(c_8694, plain, (![A_18, B_19, B_185]: (k5_xboole_0(A_18, k5_xboole_0(k4_xboole_0(B_19, A_18), k3_xboole_0(k2_xboole_0(A_18, B_19), B_185)))=k4_xboole_0(k5_xboole_0(A_18, k4_xboole_0(B_19, A_18)), B_185))), inference(superposition, [status(thm), theory('equality')], [c_18, c_8492])).
% 42.26/33.92  tff(c_84834, plain, (![A_598, B_599, B_600]: (k5_xboole_0(A_598, k5_xboole_0(k4_xboole_0(B_599, A_598), k3_xboole_0(k2_xboole_0(A_598, B_599), B_600)))=k4_xboole_0(k2_xboole_0(A_598, B_599), B_600))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8694])).
% 42.26/33.92  tff(c_85018, plain, (![B_151, A_150]: (k5_xboole_0(B_151, k4_xboole_0(A_150, k4_xboole_0(B_151, k2_xboole_0(B_151, A_150))))=k4_xboole_0(k2_xboole_0(B_151, A_150), k3_xboole_0(A_150, B_151)))), inference(superposition, [status(thm), theory('equality')], [c_6179, c_84834])).
% 42.26/33.92  tff(c_86250, plain, (![B_604, A_605]: (k4_xboole_0(k2_xboole_0(B_604, A_605), k3_xboole_0(A_605, B_604))=k5_xboole_0(B_604, A_605))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_85018])).
% 42.26/33.92  tff(c_86832, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k3_xboole_0(A_1, B_2))=k5_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_86250])).
% 42.26/33.92  tff(c_20, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_2'))!=k5_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 42.26/33.92  tff(c_158026, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86832, c_20])).
% 42.26/33.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.26/33.92  
% 42.26/33.92  Inference rules
% 42.26/33.92  ----------------------
% 42.26/33.92  #Ref     : 0
% 42.26/33.92  #Sup     : 39693
% 42.26/33.92  #Fact    : 0
% 42.26/33.92  #Define  : 0
% 42.26/33.92  #Split   : 0
% 42.26/33.92  #Chain   : 0
% 42.26/33.92  #Close   : 0
% 42.26/33.92  
% 42.26/33.92  Ordering : KBO
% 42.26/33.92  
% 42.26/33.93  Simplification rules
% 42.26/33.93  ----------------------
% 42.26/33.93  #Subsume      : 466
% 42.26/33.93  #Demod        : 59231
% 42.26/33.93  #Tautology    : 21628
% 42.26/33.93  #SimpNegUnit  : 0
% 42.26/33.93  #BackRed      : 48
% 42.26/33.93  
% 42.26/33.93  #Partial instantiations: 0
% 42.26/33.93  #Strategies tried      : 1
% 42.26/33.93  
% 42.26/33.93  Timing (in seconds)
% 42.26/33.93  ----------------------
% 42.26/33.93  Preprocessing        : 0.29
% 42.26/33.93  Parsing              : 0.15
% 42.26/33.93  CNF conversion       : 0.02
% 42.26/33.93  Main loop            : 32.89
% 42.26/33.93  Inferencing          : 3.09
% 42.26/33.93  Reduction            : 23.79
% 42.26/33.93  Demodulation         : 22.70
% 42.26/33.93  BG Simplification    : 0.49
% 42.26/33.93  Subsumption          : 4.55
% 42.26/33.93  Abstraction          : 1.03
% 42.26/33.93  MUC search           : 0.00
% 42.26/33.93  Cooper               : 0.00
% 42.26/33.93  Total                : 33.20
% 42.26/33.93  Index Insertion      : 0.00
% 42.26/33.93  Index Deletion       : 0.00
% 42.26/33.93  Index Matching       : 0.00
% 42.26/33.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
