%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:57 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  46 expanded)
%              Number of equality atoms :   33 (  45 expanded)
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

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_243,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_264,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k2_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_243])).

tff(c_268,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_264])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [B_21] : k3_xboole_0(k1_xboole_0,B_21) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_12])).

tff(c_131,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_87])).

tff(c_213,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_106])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_140,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_146,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,k3_xboole_0(A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_10])).

tff(c_508,plain,(
    ! [A_37,B_38] : k3_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_146])).

tff(c_159,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_140])).

tff(c_517,plain,(
    ! [A_37,B_38] : k4_xboole_0(k3_xboole_0(A_37,B_38),k3_xboole_0(A_37,B_38)) = k4_xboole_0(k3_xboole_0(A_37,B_38),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_159])).

tff(c_562,plain,(
    ! [A_39,B_40] : k4_xboole_0(k3_xboole_0(A_39,B_40),A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_517])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_570,plain,(
    ! [A_39,B_40] : k2_xboole_0(k4_xboole_0(A_39,k3_xboole_0(A_39,B_40)),k1_xboole_0) = k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_4])).

tff(c_607,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_8,c_570])).

tff(c_18,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:59:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.38  
% 2.57/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.38  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.57/1.38  
% 2.57/1.38  %Foreground sorts:
% 2.57/1.38  
% 2.57/1.38  
% 2.57/1.38  %Background operators:
% 2.57/1.38  
% 2.57/1.38  
% 2.57/1.38  %Foreground operators:
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.57/1.38  
% 2.57/1.39  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.57/1.39  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.57/1.39  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.57/1.39  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.57/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.57/1.39  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.57/1.39  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.57/1.39  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.57/1.39  tff(f_44, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.57/1.39  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.39  tff(c_12, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.39  tff(c_243, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.57/1.39  tff(c_264, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k2_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_243])).
% 2.57/1.39  tff(c_268, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_264])).
% 2.57/1.39  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.57/1.39  tff(c_87, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.39  tff(c_117, plain, (![B_21]: (k3_xboole_0(k1_xboole_0, B_21)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_87, c_12])).
% 2.57/1.39  tff(c_131, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_117])).
% 2.57/1.39  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.39  tff(c_106, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_87])).
% 2.57/1.39  tff(c_213, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_106])).
% 2.57/1.39  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.39  tff(c_140, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k3_xboole_0(A_22, B_23))=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.39  tff(c_146, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, k3_xboole_0(A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_10])).
% 2.57/1.39  tff(c_508, plain, (![A_37, B_38]: (k3_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_146])).
% 2.57/1.39  tff(c_159, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_140])).
% 2.57/1.39  tff(c_517, plain, (![A_37, B_38]: (k4_xboole_0(k3_xboole_0(A_37, B_38), k3_xboole_0(A_37, B_38))=k4_xboole_0(k3_xboole_0(A_37, B_38), A_37))), inference(superposition, [status(thm), theory('equality')], [c_508, c_159])).
% 2.57/1.39  tff(c_562, plain, (![A_39, B_40]: (k4_xboole_0(k3_xboole_0(A_39, B_40), A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_213, c_517])).
% 2.57/1.39  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.57/1.39  tff(c_570, plain, (![A_39, B_40]: (k2_xboole_0(k4_xboole_0(A_39, k3_xboole_0(A_39, B_40)), k1_xboole_0)=k5_xboole_0(A_39, k3_xboole_0(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_562, c_4])).
% 2.57/1.39  tff(c_607, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_8, c_570])).
% 2.57/1.39  tff(c_18, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.57/1.39  tff(c_1057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_607, c_18])).
% 2.57/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.39  
% 2.57/1.39  Inference rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Ref     : 0
% 2.57/1.39  #Sup     : 247
% 2.57/1.39  #Fact    : 0
% 2.57/1.39  #Define  : 0
% 2.57/1.39  #Split   : 0
% 2.57/1.39  #Chain   : 0
% 2.57/1.39  #Close   : 0
% 2.57/1.39  
% 2.57/1.39  Ordering : KBO
% 2.57/1.39  
% 2.57/1.39  Simplification rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Subsume      : 0
% 2.57/1.39  #Demod        : 211
% 2.57/1.39  #Tautology    : 206
% 2.57/1.39  #SimpNegUnit  : 0
% 2.57/1.39  #BackRed      : 1
% 2.57/1.39  
% 2.57/1.39  #Partial instantiations: 0
% 2.57/1.39  #Strategies tried      : 1
% 2.57/1.39  
% 2.57/1.39  Timing (in seconds)
% 2.57/1.39  ----------------------
% 2.57/1.39  Preprocessing        : 0.27
% 2.57/1.39  Parsing              : 0.16
% 2.57/1.39  CNF conversion       : 0.01
% 2.57/1.39  Main loop            : 0.32
% 2.57/1.39  Inferencing          : 0.11
% 2.57/1.39  Reduction            : 0.14
% 2.57/1.39  Demodulation         : 0.11
% 2.57/1.39  BG Simplification    : 0.01
% 2.57/1.39  Subsumption          : 0.04
% 2.57/1.39  Abstraction          : 0.02
% 2.57/1.39  MUC search           : 0.00
% 2.57/1.39  Cooper               : 0.00
% 2.57/1.39  Total                : 0.62
% 2.57/1.39  Index Insertion      : 0.00
% 2.57/1.39  Index Deletion       : 0.00
% 2.57/1.39  Index Matching       : 0.00
% 2.57/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
