%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:50 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :   57 (  90 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   50 (  83 expanded)
%              Number of equality atoms :   43 (  76 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_201,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_382,plain,(
    ! [A_48] : k4_xboole_0(A_48,A_48) = k3_xboole_0(A_48,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_201])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_388,plain,(
    ! [A_48,C_8] : k4_xboole_0(k3_xboole_0(A_48,k1_xboole_0),C_8) = k4_xboole_0(A_48,k2_xboole_0(A_48,C_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_8])).

tff(c_470,plain,(
    ! [A_52,C_53] : k4_xboole_0(k3_xboole_0(A_52,k1_xboole_0),C_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_388])).

tff(c_499,plain,(
    ! [A_52] : k3_xboole_0(A_52,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_6])).

tff(c_236,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_201])).

tff(c_598,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_236])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    ! [B_34,A_35] : k5_xboole_0(B_34,A_35) = k5_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [A_35] : k5_xboole_0(k1_xboole_0,A_35) = A_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_16])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_280,plain,(
    ! [B_43] : k3_xboole_0(k1_xboole_0,B_43) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_14])).

tff(c_24,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_285,plain,(
    ! [B_43] : k5_xboole_0(k5_xboole_0(k1_xboole_0,B_43),k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_24])).

tff(c_289,plain,(
    ! [B_43] : k2_xboole_0(k1_xboole_0,B_43) = B_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_106,c_285])).

tff(c_671,plain,(
    ! [C_59,B_60,A_61] :
      ( k4_xboole_0(k2_xboole_0(C_59,B_60),A_61) = k2_xboole_0(k4_xboole_0(C_59,A_61),B_60)
      | ~ r1_xboole_0(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_712,plain,(
    ! [A_61,B_43] :
      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,A_61),B_43) = k4_xboole_0(B_43,A_61)
      | ~ r1_xboole_0(A_61,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_671])).

tff(c_1054,plain,(
    ! [B_74,A_75] :
      ( k4_xboole_0(B_74,A_75) = B_74
      | ~ r1_xboole_0(A_75,B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_14,c_712])).

tff(c_1077,plain,(
    ! [B_76,A_77] : k4_xboole_0(B_76,k4_xboole_0(A_77,B_76)) = B_76 ),
    inference(resolution,[status(thm)],[c_18,c_1054])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1100,plain,(
    ! [B_76,A_77] : k3_xboole_0(B_76,k4_xboole_0(A_77,B_76)) = k4_xboole_0(B_76,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_12])).

tff(c_1164,plain,(
    ! [B_76,A_77] : k3_xboole_0(B_76,k4_xboole_0(A_77,B_76)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_1100])).

tff(c_528,plain,(
    ! [A_54,B_55,C_56] : k5_xboole_0(k5_xboole_0(A_54,B_55),C_56) = k5_xboole_0(A_54,k5_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4770,plain,(
    ! [A_160,B_161] : k5_xboole_0(A_160,k5_xboole_0(B_161,k3_xboole_0(A_160,B_161))) = k2_xboole_0(A_160,B_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_528])).

tff(c_4859,plain,(
    ! [B_76,A_77] : k5_xboole_0(B_76,k5_xboole_0(k4_xboole_0(A_77,B_76),k1_xboole_0)) = k2_xboole_0(B_76,k4_xboole_0(A_77,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1164,c_4770])).

tff(c_4909,plain,(
    ! [B_76,A_77] : k5_xboole_0(B_76,k4_xboole_0(A_77,B_76)) = k2_xboole_0(B_76,A_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16,c_4859])).

tff(c_26,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_1')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4909,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:29:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.83  
% 4.66/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.66/1.83  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.66/1.83  
% 4.66/1.83  %Foreground sorts:
% 4.66/1.83  
% 4.66/1.83  
% 4.66/1.83  %Background operators:
% 4.66/1.83  
% 4.66/1.83  
% 4.66/1.83  %Foreground operators:
% 4.66/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.66/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.66/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.66/1.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.66/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.66/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.66/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.66/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.66/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.66/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.66/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.66/1.83  
% 4.66/1.85  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.66/1.85  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.66/1.85  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.66/1.85  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.66/1.85  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.66/1.85  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.66/1.85  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.76/1.85  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.76/1.85  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.76/1.85  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.76/1.85  tff(f_47, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 4.76/1.85  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.76/1.85  tff(f_54, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.76/1.85  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.76/1.85  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.76/1.85  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.76/1.85  tff(c_6, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.76/1.85  tff(c_201, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.76/1.85  tff(c_382, plain, (![A_48]: (k4_xboole_0(A_48, A_48)=k3_xboole_0(A_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_201])).
% 4.76/1.85  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.76/1.85  tff(c_388, plain, (![A_48, C_8]: (k4_xboole_0(k3_xboole_0(A_48, k1_xboole_0), C_8)=k4_xboole_0(A_48, k2_xboole_0(A_48, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_382, c_8])).
% 4.76/1.85  tff(c_470, plain, (![A_52, C_53]: (k4_xboole_0(k3_xboole_0(A_52, k1_xboole_0), C_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_388])).
% 4.76/1.85  tff(c_499, plain, (![A_52]: (k3_xboole_0(A_52, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_470, c_6])).
% 4.76/1.85  tff(c_236, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_201])).
% 4.76/1.85  tff(c_598, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_499, c_236])).
% 4.76/1.85  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.76/1.85  tff(c_90, plain, (![B_34, A_35]: (k5_xboole_0(B_34, A_35)=k5_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.76/1.85  tff(c_106, plain, (![A_35]: (k5_xboole_0(k1_xboole_0, A_35)=A_35)), inference(superposition, [status(thm), theory('equality')], [c_90, c_16])).
% 4.76/1.85  tff(c_14, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.76/1.85  tff(c_280, plain, (![B_43]: (k3_xboole_0(k1_xboole_0, B_43)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_201, c_14])).
% 4.76/1.85  tff(c_24, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.76/1.85  tff(c_285, plain, (![B_43]: (k5_xboole_0(k5_xboole_0(k1_xboole_0, B_43), k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_43))), inference(superposition, [status(thm), theory('equality')], [c_280, c_24])).
% 4.76/1.85  tff(c_289, plain, (![B_43]: (k2_xboole_0(k1_xboole_0, B_43)=B_43)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_106, c_285])).
% 4.76/1.85  tff(c_671, plain, (![C_59, B_60, A_61]: (k4_xboole_0(k2_xboole_0(C_59, B_60), A_61)=k2_xboole_0(k4_xboole_0(C_59, A_61), B_60) | ~r1_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.76/1.85  tff(c_712, plain, (![A_61, B_43]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, A_61), B_43)=k4_xboole_0(B_43, A_61) | ~r1_xboole_0(A_61, B_43))), inference(superposition, [status(thm), theory('equality')], [c_289, c_671])).
% 4.76/1.85  tff(c_1054, plain, (![B_74, A_75]: (k4_xboole_0(B_74, A_75)=B_74 | ~r1_xboole_0(A_75, B_74))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_14, c_712])).
% 4.76/1.85  tff(c_1077, plain, (![B_76, A_77]: (k4_xboole_0(B_76, k4_xboole_0(A_77, B_76))=B_76)), inference(resolution, [status(thm)], [c_18, c_1054])).
% 4.76/1.85  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.76/1.85  tff(c_1100, plain, (![B_76, A_77]: (k3_xboole_0(B_76, k4_xboole_0(A_77, B_76))=k4_xboole_0(B_76, B_76))), inference(superposition, [status(thm), theory('equality')], [c_1077, c_12])).
% 4.76/1.85  tff(c_1164, plain, (![B_76, A_77]: (k3_xboole_0(B_76, k4_xboole_0(A_77, B_76))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_598, c_1100])).
% 4.76/1.85  tff(c_528, plain, (![A_54, B_55, C_56]: (k5_xboole_0(k5_xboole_0(A_54, B_55), C_56)=k5_xboole_0(A_54, k5_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.76/1.85  tff(c_4770, plain, (![A_160, B_161]: (k5_xboole_0(A_160, k5_xboole_0(B_161, k3_xboole_0(A_160, B_161)))=k2_xboole_0(A_160, B_161))), inference(superposition, [status(thm), theory('equality')], [c_24, c_528])).
% 4.76/1.85  tff(c_4859, plain, (![B_76, A_77]: (k5_xboole_0(B_76, k5_xboole_0(k4_xboole_0(A_77, B_76), k1_xboole_0))=k2_xboole_0(B_76, k4_xboole_0(A_77, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_1164, c_4770])).
% 4.76/1.85  tff(c_4909, plain, (![B_76, A_77]: (k5_xboole_0(B_76, k4_xboole_0(A_77, B_76))=k2_xboole_0(B_76, A_77))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16, c_4859])).
% 4.76/1.85  tff(c_26, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_1'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.76/1.85  tff(c_4919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4909, c_26])).
% 4.76/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.85  
% 4.76/1.85  Inference rules
% 4.76/1.85  ----------------------
% 4.76/1.85  #Ref     : 0
% 4.76/1.85  #Sup     : 1209
% 4.76/1.85  #Fact    : 0
% 4.76/1.85  #Define  : 0
% 4.76/1.85  #Split   : 0
% 4.76/1.85  #Chain   : 0
% 4.76/1.85  #Close   : 0
% 4.76/1.85  
% 4.76/1.85  Ordering : KBO
% 4.76/1.85  
% 4.76/1.85  Simplification rules
% 4.76/1.85  ----------------------
% 4.76/1.85  #Subsume      : 22
% 4.76/1.85  #Demod        : 1033
% 4.76/1.85  #Tautology    : 822
% 4.76/1.85  #SimpNegUnit  : 0
% 4.76/1.85  #BackRed      : 4
% 4.76/1.85  
% 4.76/1.85  #Partial instantiations: 0
% 4.76/1.85  #Strategies tried      : 1
% 4.76/1.85  
% 4.76/1.85  Timing (in seconds)
% 4.76/1.85  ----------------------
% 4.76/1.85  Preprocessing        : 0.29
% 4.76/1.85  Parsing              : 0.16
% 4.76/1.85  CNF conversion       : 0.01
% 4.76/1.85  Main loop            : 0.78
% 4.76/1.85  Inferencing          : 0.26
% 4.76/1.85  Reduction            : 0.34
% 4.76/1.85  Demodulation         : 0.28
% 4.76/1.85  BG Simplification    : 0.03
% 4.76/1.85  Subsumption          : 0.10
% 4.76/1.85  Abstraction          : 0.04
% 4.76/1.85  MUC search           : 0.00
% 4.76/1.85  Cooper               : 0.00
% 4.76/1.85  Total                : 1.10
% 4.76/1.85  Index Insertion      : 0.00
% 4.76/1.85  Index Deletion       : 0.00
% 4.76/1.85  Index Matching       : 0.00
% 4.76/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
