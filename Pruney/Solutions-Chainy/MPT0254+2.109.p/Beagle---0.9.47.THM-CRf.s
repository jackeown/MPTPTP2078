%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:33 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 103 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 (  86 expanded)
%              Number of equality atoms :   46 (  81 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_266,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_289,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_266])).

tff(c_292,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_289])).

tff(c_38,plain,(
    ! [B_51] : k4_xboole_0(k1_tarski(B_51),k1_tarski(B_51)) != k1_tarski(B_51) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_293,plain,(
    ! [B_51] : k1_tarski(B_51) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_38])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_554,plain,(
    ! [A_89,B_90,C_91] : k5_xboole_0(k5_xboole_0(A_89,B_90),C_91) = k5_xboole_0(A_89,k5_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2344,plain,(
    ! [A_152,B_153,C_154] : k5_xboole_0(k5_xboole_0(A_152,B_153),C_154) = k5_xboole_0(B_153,k5_xboole_0(A_152,C_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_554])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2420,plain,(
    ! [B_153,A_152] : k5_xboole_0(B_153,k5_xboole_0(A_152,k3_xboole_0(A_152,B_153))) = k2_xboole_0(A_152,B_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_2344,c_20])).

tff(c_2596,plain,(
    ! [B_155,A_156] : k5_xboole_0(B_155,k4_xboole_0(A_156,B_155)) = k2_xboole_0(A_156,B_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2420])).

tff(c_125,plain,(
    ! [B_60,A_61] : k5_xboole_0(B_60,A_61) = k5_xboole_0(A_61,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    ! [A_61] : k5_xboole_0(k1_xboole_0,A_61) = A_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_14])).

tff(c_631,plain,(
    ! [A_17,C_91] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_91)) = k5_xboole_0(k1_xboole_0,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_554])).

tff(c_644,plain,(
    ! [A_17,C_91] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_91)) = C_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_631])).

tff(c_2921,plain,(
    ! [B_161,A_162] : k5_xboole_0(B_161,k2_xboole_0(A_162,B_161)) = k4_xboole_0(A_162,B_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_2596,c_644])).

tff(c_2999,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2921])).

tff(c_3010,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2999])).

tff(c_722,plain,(
    ! [A_99,C_100] : k5_xboole_0(A_99,k5_xboole_0(A_99,C_100)) = C_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_631])).

tff(c_795,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k5_xboole_0(B_102,A_101)) = B_102 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_722])).

tff(c_831,plain,(
    ! [A_17,C_91] : k5_xboole_0(k5_xboole_0(A_17,C_91),C_91) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_795])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_223,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1138,plain,(
    ! [A_125,B_126] : k3_xboole_0(k4_xboole_0(A_125,B_126),A_125) = k4_xboole_0(A_125,B_126) ),
    inference(resolution,[status(thm)],[c_12,c_223])).

tff(c_1363,plain,(
    ! [B_133,B_134] : k3_xboole_0(B_133,k4_xboole_0(B_133,B_134)) = k4_xboole_0(B_133,B_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1138])).

tff(c_1372,plain,(
    ! [B_133,B_134] : k5_xboole_0(k5_xboole_0(B_133,k4_xboole_0(B_133,B_134)),k4_xboole_0(B_133,B_134)) = k2_xboole_0(B_133,k4_xboole_0(B_133,B_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1363,c_20])).

tff(c_1404,plain,(
    ! [B_133,B_134] : k2_xboole_0(B_133,k4_xboole_0(B_133,B_134)) = B_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_1372])).

tff(c_3035,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3010,c_1404])).

tff(c_3057,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3035])).

tff(c_3059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_3057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.76  
% 3.99/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.76  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.99/1.76  
% 3.99/1.76  %Foreground sorts:
% 3.99/1.76  
% 3.99/1.76  
% 3.99/1.76  %Background operators:
% 3.99/1.76  
% 3.99/1.76  
% 3.99/1.76  %Foreground operators:
% 3.99/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.99/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.99/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.99/1.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.99/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.99/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.99/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.99/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.99/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.99/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.99/1.76  tff('#skF_1', type, '#skF_1': $i).
% 3.99/1.76  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.99/1.76  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.99/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.99/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.99/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.99/1.76  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.99/1.76  
% 4.39/1.78  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.39/1.78  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.39/1.78  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.39/1.78  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.39/1.78  tff(f_72, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.39/1.78  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.39/1.78  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.39/1.78  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.39/1.78  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.39/1.78  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.39/1.78  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.39/1.78  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.39/1.78  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.39/1.78  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.39/1.78  tff(c_266, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.39/1.78  tff(c_289, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_266])).
% 4.39/1.78  tff(c_292, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_289])).
% 4.39/1.78  tff(c_38, plain, (![B_51]: (k4_xboole_0(k1_tarski(B_51), k1_tarski(B_51))!=k1_tarski(B_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.39/1.78  tff(c_293, plain, (![B_51]: (k1_tarski(B_51)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_292, c_38])).
% 4.39/1.78  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.39/1.78  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.39/1.78  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.39/1.78  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.39/1.78  tff(c_554, plain, (![A_89, B_90, C_91]: (k5_xboole_0(k5_xboole_0(A_89, B_90), C_91)=k5_xboole_0(A_89, k5_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.39/1.78  tff(c_2344, plain, (![A_152, B_153, C_154]: (k5_xboole_0(k5_xboole_0(A_152, B_153), C_154)=k5_xboole_0(B_153, k5_xboole_0(A_152, C_154)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_554])).
% 4.39/1.78  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.39/1.78  tff(c_2420, plain, (![B_153, A_152]: (k5_xboole_0(B_153, k5_xboole_0(A_152, k3_xboole_0(A_152, B_153)))=k2_xboole_0(A_152, B_153))), inference(superposition, [status(thm), theory('equality')], [c_2344, c_20])).
% 4.39/1.78  tff(c_2596, plain, (![B_155, A_156]: (k5_xboole_0(B_155, k4_xboole_0(A_156, B_155))=k2_xboole_0(A_156, B_155))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2420])).
% 4.39/1.78  tff(c_125, plain, (![B_60, A_61]: (k5_xboole_0(B_60, A_61)=k5_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.39/1.78  tff(c_141, plain, (![A_61]: (k5_xboole_0(k1_xboole_0, A_61)=A_61)), inference(superposition, [status(thm), theory('equality')], [c_125, c_14])).
% 4.39/1.78  tff(c_631, plain, (![A_17, C_91]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_91))=k5_xboole_0(k1_xboole_0, C_91))), inference(superposition, [status(thm), theory('equality')], [c_18, c_554])).
% 4.39/1.78  tff(c_644, plain, (![A_17, C_91]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_91))=C_91)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_631])).
% 4.39/1.78  tff(c_2921, plain, (![B_161, A_162]: (k5_xboole_0(B_161, k2_xboole_0(A_162, B_161))=k4_xboole_0(A_162, B_161))), inference(superposition, [status(thm), theory('equality')], [c_2596, c_644])).
% 4.39/1.78  tff(c_2999, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_2921])).
% 4.39/1.78  tff(c_3010, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2999])).
% 4.39/1.78  tff(c_722, plain, (![A_99, C_100]: (k5_xboole_0(A_99, k5_xboole_0(A_99, C_100))=C_100)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_631])).
% 4.39/1.78  tff(c_795, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k5_xboole_0(B_102, A_101))=B_102)), inference(superposition, [status(thm), theory('equality')], [c_4, c_722])).
% 4.39/1.78  tff(c_831, plain, (![A_17, C_91]: (k5_xboole_0(k5_xboole_0(A_17, C_91), C_91)=A_17)), inference(superposition, [status(thm), theory('equality')], [c_644, c_795])).
% 4.39/1.78  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.39/1.78  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.39/1.78  tff(c_223, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.39/1.78  tff(c_1138, plain, (![A_125, B_126]: (k3_xboole_0(k4_xboole_0(A_125, B_126), A_125)=k4_xboole_0(A_125, B_126))), inference(resolution, [status(thm)], [c_12, c_223])).
% 4.39/1.78  tff(c_1363, plain, (![B_133, B_134]: (k3_xboole_0(B_133, k4_xboole_0(B_133, B_134))=k4_xboole_0(B_133, B_134))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1138])).
% 4.39/1.78  tff(c_1372, plain, (![B_133, B_134]: (k5_xboole_0(k5_xboole_0(B_133, k4_xboole_0(B_133, B_134)), k4_xboole_0(B_133, B_134))=k2_xboole_0(B_133, k4_xboole_0(B_133, B_134)))), inference(superposition, [status(thm), theory('equality')], [c_1363, c_20])).
% 4.39/1.78  tff(c_1404, plain, (![B_133, B_134]: (k2_xboole_0(B_133, k4_xboole_0(B_133, B_134))=B_133)), inference(demodulation, [status(thm), theory('equality')], [c_831, c_1372])).
% 4.39/1.78  tff(c_3035, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3010, c_1404])).
% 4.39/1.78  tff(c_3057, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3035])).
% 4.39/1.78  tff(c_3059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_293, c_3057])).
% 4.39/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.78  
% 4.39/1.78  Inference rules
% 4.39/1.78  ----------------------
% 4.39/1.78  #Ref     : 0
% 4.39/1.78  #Sup     : 761
% 4.39/1.78  #Fact    : 0
% 4.39/1.78  #Define  : 0
% 4.39/1.78  #Split   : 0
% 4.39/1.78  #Chain   : 0
% 4.39/1.78  #Close   : 0
% 4.39/1.78  
% 4.39/1.78  Ordering : KBO
% 4.39/1.78  
% 4.39/1.78  Simplification rules
% 4.39/1.78  ----------------------
% 4.39/1.78  #Subsume      : 41
% 4.39/1.78  #Demod        : 521
% 4.39/1.78  #Tautology    : 422
% 4.39/1.78  #SimpNegUnit  : 3
% 4.39/1.78  #BackRed      : 2
% 4.39/1.78  
% 4.39/1.78  #Partial instantiations: 0
% 4.39/1.78  #Strategies tried      : 1
% 4.39/1.78  
% 4.39/1.78  Timing (in seconds)
% 4.39/1.78  ----------------------
% 4.39/1.78  Preprocessing        : 0.33
% 4.39/1.78  Parsing              : 0.18
% 4.39/1.78  CNF conversion       : 0.02
% 4.39/1.78  Main loop            : 0.68
% 4.39/1.78  Inferencing          : 0.21
% 4.39/1.78  Reduction            : 0.30
% 4.39/1.78  Demodulation         : 0.26
% 4.39/1.78  BG Simplification    : 0.03
% 4.39/1.78  Subsumption          : 0.10
% 4.39/1.78  Abstraction          : 0.04
% 4.39/1.78  MUC search           : 0.00
% 4.39/1.78  Cooper               : 0.00
% 4.39/1.78  Total                : 1.05
% 4.39/1.78  Index Insertion      : 0.00
% 4.39/1.78  Index Deletion       : 0.00
% 4.39/1.78  Index Matching       : 0.00
% 4.39/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
