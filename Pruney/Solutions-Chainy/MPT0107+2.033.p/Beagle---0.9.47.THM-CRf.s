%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:57 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   37 (  52 expanded)
%              Number of equality atoms :   36 (  51 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k2_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_135,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_132])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [B_23] : k3_xboole_0(k1_xboole_0,B_23) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_14])).

tff(c_150,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_106,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_273,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_106])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_204,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_213,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,k3_xboole_0(A_26,B_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_12])).

tff(c_484,plain,(
    ! [A_37,B_38] : k3_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_213])).

tff(c_232,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_204])).

tff(c_493,plain,(
    ! [A_37,B_38] : k4_xboole_0(k3_xboole_0(A_37,B_38),k3_xboole_0(A_37,B_38)) = k4_xboole_0(k3_xboole_0(A_37,B_38),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_232])).

tff(c_541,plain,(
    ! [A_39,B_40] : k4_xboole_0(k3_xboole_0(A_39,B_40),A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_493])).

tff(c_16,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_546,plain,(
    ! [A_39,B_40] : k2_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k5_xboole_0(A_39,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_16])).

tff(c_588,plain,(
    ! [A_41,B_42] : k2_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_546])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_594,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k3_xboole_0(A_41,k3_xboole_0(A_41,B_42))) = k5_xboole_0(A_41,k3_xboole_0(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_4])).

tff(c_617,plain,(
    ! [A_41,B_42] : k5_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_594])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.34  
% 2.64/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.35  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.64/1.35  
% 2.64/1.35  %Foreground sorts:
% 2.64/1.35  
% 2.64/1.35  
% 2.64/1.35  %Background operators:
% 2.64/1.35  
% 2.64/1.35  
% 2.64/1.35  %Foreground operators:
% 2.64/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.64/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.64/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.64/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.64/1.35  
% 2.64/1.36  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.64/1.36  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.64/1.36  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.64/1.36  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.64/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.64/1.36  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.64/1.36  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.64/1.36  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 2.64/1.36  tff(f_44, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.64/1.36  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.36  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.36  tff(c_14, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.64/1.36  tff(c_117, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.64/1.36  tff(c_132, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k2_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_117])).
% 2.64/1.36  tff(c_135, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_132])).
% 2.64/1.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.64/1.36  tff(c_87, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.64/1.36  tff(c_136, plain, (![B_23]: (k3_xboole_0(k1_xboole_0, B_23)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_87, c_14])).
% 2.64/1.36  tff(c_150, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_136])).
% 2.64/1.36  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.36  tff(c_106, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_87])).
% 2.64/1.36  tff(c_273, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_150, c_106])).
% 2.64/1.36  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.64/1.36  tff(c_204, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.64/1.36  tff(c_213, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, k3_xboole_0(A_26, B_27)))), inference(superposition, [status(thm), theory('equality')], [c_204, c_12])).
% 2.64/1.36  tff(c_484, plain, (![A_37, B_38]: (k3_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_213])).
% 2.64/1.36  tff(c_232, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_204])).
% 2.64/1.36  tff(c_493, plain, (![A_37, B_38]: (k4_xboole_0(k3_xboole_0(A_37, B_38), k3_xboole_0(A_37, B_38))=k4_xboole_0(k3_xboole_0(A_37, B_38), A_37))), inference(superposition, [status(thm), theory('equality')], [c_484, c_232])).
% 2.64/1.36  tff(c_541, plain, (![A_39, B_40]: (k4_xboole_0(k3_xboole_0(A_39, B_40), A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_273, c_493])).
% 2.64/1.36  tff(c_16, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.64/1.36  tff(c_546, plain, (![A_39, B_40]: (k2_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k5_xboole_0(A_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_541, c_16])).
% 2.64/1.36  tff(c_588, plain, (![A_41, B_42]: (k2_xboole_0(A_41, k3_xboole_0(A_41, B_42))=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_546])).
% 2.64/1.36  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(A_3, B_4))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.64/1.36  tff(c_594, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k3_xboole_0(A_41, k3_xboole_0(A_41, B_42)))=k5_xboole_0(A_41, k3_xboole_0(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_588, c_4])).
% 2.64/1.36  tff(c_617, plain, (![A_41, B_42]: (k5_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_594])).
% 2.64/1.36  tff(c_18, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.64/1.36  tff(c_1227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_617, c_18])).
% 2.64/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.36  
% 2.64/1.36  Inference rules
% 2.64/1.36  ----------------------
% 2.64/1.36  #Ref     : 0
% 2.64/1.36  #Sup     : 291
% 2.64/1.36  #Fact    : 0
% 2.64/1.36  #Define  : 0
% 2.64/1.36  #Split   : 0
% 2.64/1.36  #Chain   : 0
% 2.64/1.36  #Close   : 0
% 2.64/1.36  
% 2.64/1.36  Ordering : KBO
% 2.64/1.36  
% 2.64/1.36  Simplification rules
% 2.64/1.36  ----------------------
% 2.64/1.36  #Subsume      : 0
% 2.64/1.36  #Demod        : 283
% 2.64/1.36  #Tautology    : 239
% 2.64/1.36  #SimpNegUnit  : 0
% 2.64/1.36  #BackRed      : 1
% 2.64/1.36  
% 2.64/1.36  #Partial instantiations: 0
% 2.64/1.36  #Strategies tried      : 1
% 2.64/1.36  
% 2.64/1.36  Timing (in seconds)
% 2.64/1.36  ----------------------
% 2.64/1.36  Preprocessing        : 0.26
% 2.64/1.36  Parsing              : 0.14
% 2.64/1.36  CNF conversion       : 0.01
% 2.64/1.36  Main loop            : 0.34
% 2.64/1.36  Inferencing          : 0.12
% 2.64/1.36  Reduction            : 0.15
% 2.64/1.36  Demodulation         : 0.13
% 2.64/1.36  BG Simplification    : 0.01
% 2.64/1.36  Subsumption          : 0.04
% 2.64/1.36  Abstraction          : 0.02
% 2.64/1.36  MUC search           : 0.00
% 2.64/1.36  Cooper               : 0.00
% 2.64/1.36  Total                : 0.63
% 2.64/1.36  Index Insertion      : 0.00
% 2.64/1.36  Index Deletion       : 0.00
% 2.64/1.36  Index Matching       : 0.00
% 2.64/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
