%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:45 EST 2020

% Result     : Theorem 9.33s
% Output     : CNFRefutation 9.45s
% Verified   : 
% Statistics : Number of formulae       :   44 (  82 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   34 (  72 expanded)
%              Number of equality atoms :   33 (  71 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_85])).

tff(c_104,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_100])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = k3_xboole_0(A_23,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_10])).

tff(c_121,plain,(
    ! [A_23] : k3_xboole_0(A_23,A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_109])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_144,plain,(
    ! [A_25,B_26] : k5_xboole_0(k5_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_183,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_12,A_12)) = k2_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_144])).

tff(c_187,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_4,c_183])).

tff(c_278,plain,(
    ! [A_29,B_30,C_31] : k5_xboole_0(k5_xboole_0(A_29,B_30),C_31) = k5_xboole_0(A_29,k5_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_344,plain,(
    ! [A_12,C_31] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_31)) = k5_xboole_0(k1_xboole_0,C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_278])).

tff(c_357,plain,(
    ! [A_12,C_31] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_31)) = C_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_344])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k5_xboole_0(k5_xboole_0(A_9,B_10),C_11) = k5_xboole_0(A_9,k5_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2325,plain,(
    ! [B_60,A_61] : k5_xboole_0(k5_xboole_0(B_60,A_61),k3_xboole_0(A_61,B_60)) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_144])).

tff(c_3537,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k5_xboole_0(B_71,k3_xboole_0(B_71,A_70))) = k2_xboole_0(B_71,A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2325])).

tff(c_3600,plain,(
    ! [B_71,A_70] : k5_xboole_0(B_71,k3_xboole_0(B_71,A_70)) = k5_xboole_0(A_70,k2_xboole_0(B_71,A_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3537,c_357])).

tff(c_18,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_2'))) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_12809,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2'))) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3600,c_19])).

tff(c_12812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_12809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:42:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.33/4.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.33/4.06  
% 9.33/4.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.33/4.06  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 9.33/4.06  
% 9.33/4.06  %Foreground sorts:
% 9.33/4.06  
% 9.33/4.06  
% 9.33/4.06  %Background operators:
% 9.33/4.06  
% 9.33/4.06  
% 9.33/4.06  %Foreground operators:
% 9.33/4.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.33/4.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.33/4.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.33/4.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.33/4.06  tff('#skF_2', type, '#skF_2': $i).
% 9.33/4.06  tff('#skF_1', type, '#skF_1': $i).
% 9.33/4.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.33/4.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.33/4.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.33/4.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.33/4.06  
% 9.45/4.07  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.45/4.07  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.45/4.07  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.45/4.07  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 9.45/4.07  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.45/4.07  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 9.45/4.07  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.45/4.07  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.45/4.07  tff(f_44, negated_conjecture, ~(![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 9.45/4.07  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.45/4.07  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.45/4.07  tff(c_85, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.45/4.07  tff(c_100, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_85])).
% 9.45/4.07  tff(c_104, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_100])).
% 9.45/4.07  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.45/4.07  tff(c_109, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=k3_xboole_0(A_23, A_23))), inference(superposition, [status(thm), theory('equality')], [c_104, c_10])).
% 9.45/4.07  tff(c_121, plain, (![A_23]: (k3_xboole_0(A_23, A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_109])).
% 9.45/4.07  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.45/4.07  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.45/4.07  tff(c_144, plain, (![A_25, B_26]: (k5_xboole_0(k5_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.45/4.07  tff(c_183, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_12, A_12))=k2_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_144])).
% 9.45/4.07  tff(c_187, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_4, c_183])).
% 9.45/4.07  tff(c_278, plain, (![A_29, B_30, C_31]: (k5_xboole_0(k5_xboole_0(A_29, B_30), C_31)=k5_xboole_0(A_29, k5_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.45/4.07  tff(c_344, plain, (![A_12, C_31]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_31))=k5_xboole_0(k1_xboole_0, C_31))), inference(superposition, [status(thm), theory('equality')], [c_14, c_278])).
% 9.45/4.07  tff(c_357, plain, (![A_12, C_31]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_31))=C_31)), inference(demodulation, [status(thm), theory('equality')], [c_187, c_344])).
% 9.45/4.07  tff(c_12, plain, (![A_9, B_10, C_11]: (k5_xboole_0(k5_xboole_0(A_9, B_10), C_11)=k5_xboole_0(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.45/4.07  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.45/4.07  tff(c_2325, plain, (![B_60, A_61]: (k5_xboole_0(k5_xboole_0(B_60, A_61), k3_xboole_0(A_61, B_60))=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_2, c_144])).
% 9.45/4.07  tff(c_3537, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k5_xboole_0(B_71, k3_xboole_0(B_71, A_70)))=k2_xboole_0(B_71, A_70))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2325])).
% 9.45/4.07  tff(c_3600, plain, (![B_71, A_70]: (k5_xboole_0(B_71, k3_xboole_0(B_71, A_70))=k5_xboole_0(A_70, k2_xboole_0(B_71, A_70)))), inference(superposition, [status(thm), theory('equality')], [c_3537, c_357])).
% 9.45/4.07  tff(c_18, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.45/4.07  tff(c_19, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_2')))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 9.45/4.07  tff(c_12809, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2')))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3600, c_19])).
% 9.45/4.07  tff(c_12812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_12809])).
% 9.45/4.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.45/4.07  
% 9.45/4.07  Inference rules
% 9.45/4.07  ----------------------
% 9.45/4.07  #Ref     : 0
% 9.45/4.07  #Sup     : 3371
% 9.45/4.07  #Fact    : 0
% 9.45/4.07  #Define  : 0
% 9.45/4.07  #Split   : 0
% 9.45/4.07  #Chain   : 0
% 9.45/4.07  #Close   : 0
% 9.45/4.07  
% 9.45/4.07  Ordering : KBO
% 9.45/4.07  
% 9.45/4.07  Simplification rules
% 9.45/4.07  ----------------------
% 9.45/4.07  #Subsume      : 215
% 9.45/4.07  #Demod        : 3927
% 9.45/4.07  #Tautology    : 1070
% 9.45/4.07  #SimpNegUnit  : 0
% 9.45/4.07  #BackRed      : 1
% 9.45/4.07  
% 9.45/4.07  #Partial instantiations: 0
% 9.45/4.07  #Strategies tried      : 1
% 9.45/4.07  
% 9.45/4.07  Timing (in seconds)
% 9.45/4.07  ----------------------
% 9.45/4.08  Preprocessing        : 0.26
% 9.45/4.08  Parsing              : 0.14
% 9.45/4.08  CNF conversion       : 0.01
% 9.45/4.08  Main loop            : 3.07
% 9.45/4.08  Inferencing          : 0.55
% 9.45/4.08  Reduction            : 2.08
% 9.45/4.08  Demodulation         : 1.96
% 9.45/4.08  BG Simplification    : 0.09
% 9.45/4.08  Subsumption          : 0.26
% 9.45/4.08  Abstraction          : 0.13
% 9.45/4.08  MUC search           : 0.00
% 9.45/4.08  Cooper               : 0.00
% 9.45/4.08  Total                : 3.35
% 9.45/4.08  Index Insertion      : 0.00
% 9.45/4.08  Index Deletion       : 0.00
% 9.45/4.08  Index Matching       : 0.00
% 9.45/4.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
