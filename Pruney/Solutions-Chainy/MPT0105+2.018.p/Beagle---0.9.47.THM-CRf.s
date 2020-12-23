%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:49 EST 2020

% Result     : Theorem 5.65s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   36 (  53 expanded)
%              Number of equality atoms :   35 (  52 expanded)
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

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_6,plain,(
    ! [A_4,B_5] : k2_xboole_0(A_4,k4_xboole_0(B_5,A_4)) = k2_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_147])).

tff(c_165,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_162])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_253,plain,(
    ! [A_33,B_34] : k5_xboole_0(k5_xboole_0(A_33,B_34),k3_xboole_0(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_280,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_253])).

tff(c_292,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_280])).

tff(c_217,plain,(
    ! [A_30,B_31] : k2_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_217])).

tff(c_295,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_226])).

tff(c_612,plain,(
    ! [A_46,B_47,C_48] : k4_xboole_0(k4_xboole_0(A_46,B_47),C_48) = k4_xboole_0(A_46,k2_xboole_0(B_47,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7661,plain,(
    ! [A_171,B_172,C_173] : k4_xboole_0(k4_xboole_0(A_171,B_172),k4_xboole_0(A_171,k2_xboole_0(B_172,C_173))) = k3_xboole_0(k4_xboole_0(A_171,B_172),C_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_12])).

tff(c_7866,plain,(
    ! [A_171,A_6] : k4_xboole_0(k4_xboole_0(A_171,A_6),k4_xboole_0(A_171,A_6)) = k3_xboole_0(k4_xboole_0(A_171,A_6),A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_7661])).

tff(c_7949,plain,(
    ! [A_174,A_175] : k3_xboole_0(A_174,k4_xboole_0(A_175,A_174)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_2,c_7866])).

tff(c_325,plain,(
    ! [A_37,B_38,C_39] : k5_xboole_0(k5_xboole_0(A_37,B_38),C_39) = k5_xboole_0(A_37,k5_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_338,plain,(
    ! [A_37,B_38] : k5_xboole_0(A_37,k5_xboole_0(B_38,k3_xboole_0(A_37,B_38))) = k2_xboole_0(A_37,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_20])).

tff(c_7994,plain,(
    ! [A_174,A_175] : k5_xboole_0(A_174,k5_xboole_0(k4_xboole_0(A_175,A_174),k1_xboole_0)) = k2_xboole_0(A_174,k4_xboole_0(A_175,A_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7949,c_338])).

tff(c_8090,plain,(
    ! [A_174,A_175] : k5_xboole_0(A_174,k4_xboole_0(A_175,A_174)) = k2_xboole_0(A_174,A_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14,c_7994])).

tff(c_22,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_9017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8090,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:51:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.65/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.37  
% 5.65/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.37  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 5.81/2.37  
% 5.81/2.37  %Foreground sorts:
% 5.81/2.37  
% 5.81/2.37  
% 5.81/2.37  %Background operators:
% 5.81/2.37  
% 5.81/2.37  
% 5.81/2.37  %Foreground operators:
% 5.81/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.81/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.81/2.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.81/2.37  tff('#skF_2', type, '#skF_2': $i).
% 5.81/2.37  tff('#skF_1', type, '#skF_1': $i).
% 5.81/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.81/2.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.81/2.37  
% 5.81/2.38  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.81/2.38  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.81/2.38  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.81/2.38  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.81/2.38  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.81/2.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.81/2.38  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.81/2.38  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.81/2.38  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.81/2.38  tff(f_48, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.81/2.38  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, k4_xboole_0(B_5, A_4))=k2_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.81/2.38  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.81/2.38  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.81/2.38  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.81/2.38  tff(c_147, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.81/2.38  tff(c_162, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_147])).
% 5.81/2.38  tff(c_165, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_162])).
% 5.81/2.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.81/2.38  tff(c_253, plain, (![A_33, B_34]: (k5_xboole_0(k5_xboole_0(A_33, B_34), k3_xboole_0(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.38  tff(c_280, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_253])).
% 5.81/2.38  tff(c_292, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_280])).
% 5.81/2.38  tff(c_217, plain, (![A_30, B_31]: (k2_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.81/2.38  tff(c_226, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_165, c_217])).
% 5.81/2.38  tff(c_295, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_292, c_226])).
% 5.81/2.38  tff(c_612, plain, (![A_46, B_47, C_48]: (k4_xboole_0(k4_xboole_0(A_46, B_47), C_48)=k4_xboole_0(A_46, k2_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.81/2.38  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.81/2.38  tff(c_7661, plain, (![A_171, B_172, C_173]: (k4_xboole_0(k4_xboole_0(A_171, B_172), k4_xboole_0(A_171, k2_xboole_0(B_172, C_173)))=k3_xboole_0(k4_xboole_0(A_171, B_172), C_173))), inference(superposition, [status(thm), theory('equality')], [c_612, c_12])).
% 5.81/2.38  tff(c_7866, plain, (![A_171, A_6]: (k4_xboole_0(k4_xboole_0(A_171, A_6), k4_xboole_0(A_171, A_6))=k3_xboole_0(k4_xboole_0(A_171, A_6), A_6))), inference(superposition, [status(thm), theory('equality')], [c_295, c_7661])).
% 5.81/2.38  tff(c_7949, plain, (![A_174, A_175]: (k3_xboole_0(A_174, k4_xboole_0(A_175, A_174))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_2, c_7866])).
% 5.81/2.38  tff(c_325, plain, (![A_37, B_38, C_39]: (k5_xboole_0(k5_xboole_0(A_37, B_38), C_39)=k5_xboole_0(A_37, k5_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.81/2.38  tff(c_20, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.38  tff(c_338, plain, (![A_37, B_38]: (k5_xboole_0(A_37, k5_xboole_0(B_38, k3_xboole_0(A_37, B_38)))=k2_xboole_0(A_37, B_38))), inference(superposition, [status(thm), theory('equality')], [c_325, c_20])).
% 5.81/2.38  tff(c_7994, plain, (![A_174, A_175]: (k5_xboole_0(A_174, k5_xboole_0(k4_xboole_0(A_175, A_174), k1_xboole_0))=k2_xboole_0(A_174, k4_xboole_0(A_175, A_174)))), inference(superposition, [status(thm), theory('equality')], [c_7949, c_338])).
% 5.81/2.38  tff(c_8090, plain, (![A_174, A_175]: (k5_xboole_0(A_174, k4_xboole_0(A_175, A_174))=k2_xboole_0(A_174, A_175))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14, c_7994])).
% 5.81/2.38  tff(c_22, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.81/2.38  tff(c_9017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8090, c_22])).
% 5.81/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.38  
% 5.81/2.38  Inference rules
% 5.81/2.38  ----------------------
% 5.81/2.38  #Ref     : 0
% 5.81/2.38  #Sup     : 2224
% 5.81/2.38  #Fact    : 0
% 5.81/2.38  #Define  : 0
% 5.81/2.38  #Split   : 0
% 5.81/2.38  #Chain   : 0
% 5.81/2.38  #Close   : 0
% 5.81/2.38  
% 5.81/2.38  Ordering : KBO
% 5.81/2.38  
% 5.81/2.38  Simplification rules
% 5.81/2.38  ----------------------
% 5.81/2.38  #Subsume      : 4
% 5.81/2.38  #Demod        : 2251
% 5.81/2.38  #Tautology    : 1572
% 5.81/2.38  #SimpNegUnit  : 0
% 5.81/2.38  #BackRed      : 9
% 5.81/2.38  
% 5.81/2.38  #Partial instantiations: 0
% 5.81/2.38  #Strategies tried      : 1
% 5.81/2.38  
% 5.81/2.38  Timing (in seconds)
% 5.81/2.38  ----------------------
% 5.81/2.39  Preprocessing        : 0.30
% 5.81/2.39  Parsing              : 0.16
% 5.81/2.39  CNF conversion       : 0.02
% 5.81/2.39  Main loop            : 1.27
% 5.81/2.39  Inferencing          : 0.39
% 5.81/2.39  Reduction            : 0.62
% 5.81/2.39  Demodulation         : 0.53
% 5.81/2.39  BG Simplification    : 0.04
% 5.81/2.39  Subsumption          : 0.15
% 5.81/2.39  Abstraction          : 0.07
% 5.81/2.39  MUC search           : 0.00
% 5.81/2.39  Cooper               : 0.00
% 5.81/2.39  Total                : 1.61
% 5.81/2.39  Index Insertion      : 0.00
% 5.81/2.39  Index Deletion       : 0.00
% 5.81/2.39  Index Matching       : 0.00
% 5.81/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
