%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:01 EST 2020

% Result     : Theorem 34.35s
% Output     : CNFRefutation 34.35s
% Verified   : 
% Statistics : Number of formulae       :   60 (  86 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  81 expanded)
%              Number of equality atoms :   44 (  69 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_632,plain,(
    ! [A_49,B_50,C_51] : k4_xboole_0(k4_xboole_0(A_49,B_50),C_51) = k4_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10308,plain,(
    ! [A_163,B_164,C_165] : k4_xboole_0(A_163,k2_xboole_0(k4_xboole_0(A_163,B_164),C_165)) = k4_xboole_0(k3_xboole_0(A_163,B_164),C_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_632])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_165,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_173,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_165])).

tff(c_390,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_411,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_390])).

tff(c_429,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_411])).

tff(c_790,plain,(
    ! [C_54] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_54)) = k4_xboole_0('#skF_1',C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_632])).

tff(c_840,plain,(
    ! [B_2] : k4_xboole_0('#skF_1',k2_xboole_0(B_2,'#skF_2')) = k4_xboole_0('#skF_1',B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_790])).

tff(c_10360,plain,(
    ! [B_164] : k4_xboole_0(k3_xboole_0('#skF_1',B_164),'#skF_2') = k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',B_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10308,c_840])).

tff(c_78175,plain,(
    ! [B_469] : k4_xboole_0(k3_xboole_0('#skF_1',B_469),'#skF_2') = k3_xboole_0('#skF_1',B_469) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_10360])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_191,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_209,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_191])).

tff(c_213,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_209])).

tff(c_646,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k2_xboole_0(B_50,k4_xboole_0(A_49,B_50))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_213])).

tff(c_707,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k2_xboole_0(B_50,A_49)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_646])).

tff(c_22,plain,(
    ! [A_18,B_19] : k2_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_402,plain,(
    ! [A_41,B_42] : k2_xboole_0(k3_xboole_0(A_41,B_42),k4_xboole_0(A_41,B_42)) = k2_xboole_0(k3_xboole_0(A_41,B_42),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_12])).

tff(c_426,plain,(
    ! [A_41,B_42] : k2_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_402])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k4_xboole_0(A_11,B_12),C_13) = k4_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_656,plain,(
    ! [A_49,B_50,B_17] : k4_xboole_0(A_49,k2_xboole_0(B_50,k4_xboole_0(k4_xboole_0(A_49,B_50),B_17))) = k3_xboole_0(k4_xboole_0(A_49,B_50),B_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_20])).

tff(c_19444,plain,(
    ! [A_225,B_226,B_227] : k4_xboole_0(A_225,k2_xboole_0(B_226,k4_xboole_0(A_225,k2_xboole_0(B_226,B_227)))) = k3_xboole_0(k4_xboole_0(A_225,B_226),B_227) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_656])).

tff(c_19820,plain,(
    ! [A_225,A_41,B_42] : k4_xboole_0(A_225,k2_xboole_0(A_41,k4_xboole_0(A_225,A_41))) = k3_xboole_0(k4_xboole_0(A_225,A_41),k3_xboole_0(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_19444])).

tff(c_21359,plain,(
    ! [A_233,A_234,B_235] : k3_xboole_0(k4_xboole_0(A_233,A_234),k3_xboole_0(A_234,B_235)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_707,c_12,c_19820])).

tff(c_21757,plain,(
    ! [A_233,B_4,A_3] : k3_xboole_0(k4_xboole_0(A_233,B_4),k3_xboole_0(A_3,B_4)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_21359])).

tff(c_78289,plain,(
    ! [B_469,A_3] : k3_xboole_0(k3_xboole_0('#skF_1',B_469),k3_xboole_0(A_3,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78175,c_21757])).

tff(c_160,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_164,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_160,c_27])).

tff(c_158863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78289,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:55:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.35/27.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.35/27.15  
% 34.35/27.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.35/27.16  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 34.35/27.16  
% 34.35/27.16  %Foreground sorts:
% 34.35/27.16  
% 34.35/27.16  
% 34.35/27.16  %Background operators:
% 34.35/27.16  
% 34.35/27.16  
% 34.35/27.16  %Foreground operators:
% 34.35/27.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.35/27.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 34.35/27.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 34.35/27.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 34.35/27.16  tff('#skF_2', type, '#skF_2': $i).
% 34.35/27.16  tff('#skF_3', type, '#skF_3': $i).
% 34.35/27.16  tff('#skF_1', type, '#skF_1': $i).
% 34.35/27.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.35/27.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.35/27.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 34.35/27.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 34.35/27.16  
% 34.35/27.17  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 34.35/27.17  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 34.35/27.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 34.35/27.17  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 34.35/27.17  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 34.35/27.17  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 34.35/27.17  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 34.35/27.17  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 34.35/27.17  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 34.35/27.17  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 34.35/27.17  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 34.35/27.17  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 34.35/27.17  tff(c_632, plain, (![A_49, B_50, C_51]: (k4_xboole_0(k4_xboole_0(A_49, B_50), C_51)=k4_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 34.35/27.17  tff(c_10308, plain, (![A_163, B_164, C_165]: (k4_xboole_0(A_163, k2_xboole_0(k4_xboole_0(A_163, B_164), C_165))=k4_xboole_0(k3_xboole_0(A_163, B_164), C_165))), inference(superposition, [status(thm), theory('equality')], [c_20, c_632])).
% 34.35/27.17  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 34.35/27.17  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 34.35/27.17  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 34.35/27.17  tff(c_165, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_33])).
% 34.35/27.17  tff(c_173, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_165])).
% 34.35/27.17  tff(c_390, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 34.35/27.17  tff(c_411, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_173, c_390])).
% 34.35/27.17  tff(c_429, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_411])).
% 34.35/27.17  tff(c_790, plain, (![C_54]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_54))=k4_xboole_0('#skF_1', C_54))), inference(superposition, [status(thm), theory('equality')], [c_429, c_632])).
% 34.35/27.17  tff(c_840, plain, (![B_2]: (k4_xboole_0('#skF_1', k2_xboole_0(B_2, '#skF_2'))=k4_xboole_0('#skF_1', B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_790])).
% 34.35/27.17  tff(c_10360, plain, (![B_164]: (k4_xboole_0(k3_xboole_0('#skF_1', B_164), '#skF_2')=k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', B_164)))), inference(superposition, [status(thm), theory('equality')], [c_10308, c_840])).
% 34.35/27.17  tff(c_78175, plain, (![B_469]: (k4_xboole_0(k3_xboole_0('#skF_1', B_469), '#skF_2')=k3_xboole_0('#skF_1', B_469))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_10360])).
% 34.35/27.17  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 34.35/27.17  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 34.35/27.17  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 34.35/27.17  tff(c_191, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 34.35/27.17  tff(c_209, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_191])).
% 34.35/27.17  tff(c_213, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_209])).
% 34.35/27.17  tff(c_646, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k2_xboole_0(B_50, k4_xboole_0(A_49, B_50)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_632, c_213])).
% 34.35/27.17  tff(c_707, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k2_xboole_0(B_50, A_49))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_646])).
% 34.35/27.17  tff(c_22, plain, (![A_18, B_19]: (k2_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_47])).
% 34.35/27.17  tff(c_402, plain, (![A_41, B_42]: (k2_xboole_0(k3_xboole_0(A_41, B_42), k4_xboole_0(A_41, B_42))=k2_xboole_0(k3_xboole_0(A_41, B_42), A_41))), inference(superposition, [status(thm), theory('equality')], [c_390, c_12])).
% 34.35/27.17  tff(c_426, plain, (![A_41, B_42]: (k2_xboole_0(A_41, k3_xboole_0(A_41, B_42))=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_402])).
% 34.35/27.17  tff(c_16, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k4_xboole_0(A_11, B_12), C_13)=k4_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 34.35/27.17  tff(c_656, plain, (![A_49, B_50, B_17]: (k4_xboole_0(A_49, k2_xboole_0(B_50, k4_xboole_0(k4_xboole_0(A_49, B_50), B_17)))=k3_xboole_0(k4_xboole_0(A_49, B_50), B_17))), inference(superposition, [status(thm), theory('equality')], [c_632, c_20])).
% 34.35/27.17  tff(c_19444, plain, (![A_225, B_226, B_227]: (k4_xboole_0(A_225, k2_xboole_0(B_226, k4_xboole_0(A_225, k2_xboole_0(B_226, B_227))))=k3_xboole_0(k4_xboole_0(A_225, B_226), B_227))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_656])).
% 34.35/27.17  tff(c_19820, plain, (![A_225, A_41, B_42]: (k4_xboole_0(A_225, k2_xboole_0(A_41, k4_xboole_0(A_225, A_41)))=k3_xboole_0(k4_xboole_0(A_225, A_41), k3_xboole_0(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_426, c_19444])).
% 34.35/27.17  tff(c_21359, plain, (![A_233, A_234, B_235]: (k3_xboole_0(k4_xboole_0(A_233, A_234), k3_xboole_0(A_234, B_235))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_707, c_12, c_19820])).
% 34.35/27.17  tff(c_21757, plain, (![A_233, B_4, A_3]: (k3_xboole_0(k4_xboole_0(A_233, B_4), k3_xboole_0(A_3, B_4))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_21359])).
% 34.35/27.17  tff(c_78289, plain, (![B_469, A_3]: (k3_xboole_0(k3_xboole_0('#skF_1', B_469), k3_xboole_0(A_3, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78175, c_21757])).
% 34.35/27.17  tff(c_160, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 34.35/27.17  tff(c_24, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 34.35/27.17  tff(c_27, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_24])).
% 34.35/27.17  tff(c_164, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_160, c_27])).
% 34.35/27.17  tff(c_158863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78289, c_164])).
% 34.35/27.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.35/27.17  
% 34.35/27.17  Inference rules
% 34.35/27.17  ----------------------
% 34.35/27.17  #Ref     : 0
% 34.35/27.17  #Sup     : 39027
% 34.35/27.17  #Fact    : 0
% 34.35/27.17  #Define  : 0
% 34.35/27.17  #Split   : 0
% 34.35/27.17  #Chain   : 0
% 34.35/27.17  #Close   : 0
% 34.35/27.17  
% 34.35/27.17  Ordering : KBO
% 34.35/27.17  
% 34.35/27.17  Simplification rules
% 34.35/27.17  ----------------------
% 34.35/27.17  #Subsume      : 104
% 34.35/27.17  #Demod        : 53245
% 34.35/27.17  #Tautology    : 27078
% 34.35/27.17  #SimpNegUnit  : 0
% 34.35/27.17  #BackRed      : 25
% 34.35/27.17  
% 34.35/27.17  #Partial instantiations: 0
% 34.35/27.17  #Strategies tried      : 1
% 34.35/27.17  
% 34.35/27.17  Timing (in seconds)
% 34.35/27.17  ----------------------
% 34.35/27.17  Preprocessing        : 0.27
% 34.35/27.17  Parsing              : 0.15
% 34.35/27.17  CNF conversion       : 0.02
% 34.51/27.17  Main loop            : 26.12
% 34.51/27.17  Inferencing          : 2.21
% 34.51/27.17  Reduction            : 18.55
% 34.51/27.17  Demodulation         : 17.63
% 34.51/27.17  BG Simplification    : 0.29
% 34.51/27.17  Subsumption          : 4.32
% 34.51/27.17  Abstraction          : 0.56
% 34.51/27.17  MUC search           : 0.00
% 34.51/27.17  Cooper               : 0.00
% 34.51/27.17  Total                : 26.42
% 34.51/27.17  Index Insertion      : 0.00
% 34.51/27.17  Index Deletion       : 0.00
% 34.51/27.17  Index Matching       : 0.00
% 34.51/27.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
