%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:12 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 105 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 115 expanded)
%              Number of equality atoms :   33 (  60 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_85,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_191,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_212,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_191])).

tff(c_215,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_212])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_216,plain,(
    ! [A_43,B_44] : k5_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_228,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_216])).

tff(c_460,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_228])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_172,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1678,plain,(
    ! [A_112,B_113] : k3_xboole_0(k4_xboole_0(A_112,B_113),A_112) = k4_xboole_0(A_112,B_113) ),
    inference(resolution,[status(thm)],[c_16,c_172])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1693,plain,(
    ! [A_112,B_113] : k5_xboole_0(k4_xboole_0(A_112,B_113),k4_xboole_0(A_112,B_113)) = k4_xboole_0(k4_xboole_0(A_112,B_113),A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_1678,c_6])).

tff(c_1744,plain,(
    ! [A_114,B_115] : k4_xboole_0(k4_xboole_0(A_114,B_115),A_114) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_1693])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1776,plain,(
    ! [A_114,B_115] : k2_xboole_0(A_114,k4_xboole_0(A_114,B_115)) = k2_xboole_0(A_114,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1744,c_18])).

tff(c_1847,plain,(
    ! [A_116,B_117] : k2_xboole_0(A_116,k4_xboole_0(A_116,B_117)) = A_116 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1776])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_182,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_172])).

tff(c_225,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_216])).

tff(c_441,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k5_xboole_0('#skF_1','#skF_1')) = k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_18])).

tff(c_453,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k5_xboole_0('#skF_1','#skF_1')) = k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_441])).

tff(c_1162,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_460,c_453])).

tff(c_75,plain,(
    ! [A_30,B_31] : r1_tarski(k4_xboole_0(A_30,B_31),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    ! [A_18] : r1_tarski(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_75])).

tff(c_538,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(k2_xboole_0(A_59,B_61),C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_563,plain,(
    ! [A_62,B_63] : r1_tarski(A_62,k2_xboole_0(A_62,B_63)) ),
    inference(resolution,[status(thm)],[c_78,c_538])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_891,plain,(
    ! [A_79,B_80,B_81] : r1_tarski(A_79,k2_xboole_0(k2_xboole_0(A_79,B_80),B_81)) ),
    inference(resolution,[status(thm)],[c_563,c_8])).

tff(c_929,plain,(
    ! [A_79,A_1,B_80] : r1_tarski(A_79,k2_xboole_0(A_1,k2_xboole_0(A_79,B_80))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_891])).

tff(c_1172,plain,(
    ! [A_1] : r1_tarski('#skF_1',k2_xboole_0(A_1,k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1162,c_929])).

tff(c_1857,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1847,c_1172])).

tff(c_1958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1857])).

tff(c_1959,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_26,plain,(
    ! [A_24,B_25] : r1_xboole_0(k4_xboole_0(A_24,B_25),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2421,plain,(
    ! [A_145,C_146,B_147] :
      ( r1_xboole_0(A_145,C_146)
      | ~ r1_xboole_0(B_147,C_146)
      | ~ r1_tarski(A_145,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2924,plain,(
    ! [A_164,B_165,A_166] :
      ( r1_xboole_0(A_164,B_165)
      | ~ r1_tarski(A_164,k4_xboole_0(A_166,B_165)) ) ),
    inference(resolution,[status(thm)],[c_26,c_2421])).

tff(c_2956,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_2924])).

tff(c_2974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1959,c_2956])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.55  
% 3.46/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.56  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.46/1.56  
% 3.46/1.56  %Foreground sorts:
% 3.46/1.56  
% 3.46/1.56  
% 3.46/1.56  %Background operators:
% 3.46/1.56  
% 3.46/1.56  
% 3.46/1.56  %Foreground operators:
% 3.46/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.46/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.46/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.46/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.46/1.56  
% 3.46/1.57  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.46/1.57  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.46/1.57  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.46/1.57  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.46/1.57  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.46/1.57  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.46/1.57  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.46/1.57  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.46/1.57  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.46/1.57  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.46/1.57  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.46/1.57  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.46/1.57  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.46/1.57  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.46/1.57  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.46/1.57  tff(c_85, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 3.46/1.57  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.46/1.57  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.46/1.57  tff(c_20, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.46/1.57  tff(c_191, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.46/1.57  tff(c_212, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_191])).
% 3.46/1.57  tff(c_215, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_212])).
% 3.46/1.57  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.46/1.57  tff(c_216, plain, (![A_43, B_44]: (k5_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.57  tff(c_228, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_216])).
% 3.46/1.57  tff(c_460, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_215, c_228])).
% 3.46/1.57  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.46/1.57  tff(c_172, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.46/1.57  tff(c_1678, plain, (![A_112, B_113]: (k3_xboole_0(k4_xboole_0(A_112, B_113), A_112)=k4_xboole_0(A_112, B_113))), inference(resolution, [status(thm)], [c_16, c_172])).
% 3.46/1.57  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.57  tff(c_1693, plain, (![A_112, B_113]: (k5_xboole_0(k4_xboole_0(A_112, B_113), k4_xboole_0(A_112, B_113))=k4_xboole_0(k4_xboole_0(A_112, B_113), A_112))), inference(superposition, [status(thm), theory('equality')], [c_1678, c_6])).
% 3.46/1.57  tff(c_1744, plain, (![A_114, B_115]: (k4_xboole_0(k4_xboole_0(A_114, B_115), A_114)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_460, c_1693])).
% 3.46/1.57  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.46/1.57  tff(c_1776, plain, (![A_114, B_115]: (k2_xboole_0(A_114, k4_xboole_0(A_114, B_115))=k2_xboole_0(A_114, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1744, c_18])).
% 3.46/1.57  tff(c_1847, plain, (![A_116, B_117]: (k2_xboole_0(A_116, k4_xboole_0(A_116, B_117))=A_116)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1776])).
% 3.46/1.57  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.46/1.57  tff(c_30, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.46/1.57  tff(c_182, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_30, c_172])).
% 3.46/1.57  tff(c_225, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_182, c_216])).
% 3.46/1.57  tff(c_441, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k5_xboole_0('#skF_1', '#skF_1'))=k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_225, c_18])).
% 3.46/1.57  tff(c_453, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k5_xboole_0('#skF_1', '#skF_1'))=k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_441])).
% 3.46/1.57  tff(c_1162, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_460, c_453])).
% 3.46/1.57  tff(c_75, plain, (![A_30, B_31]: (r1_tarski(k4_xboole_0(A_30, B_31), A_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.46/1.57  tff(c_78, plain, (![A_18]: (r1_tarski(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_75])).
% 3.46/1.57  tff(c_538, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(k2_xboole_0(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.57  tff(c_563, plain, (![A_62, B_63]: (r1_tarski(A_62, k2_xboole_0(A_62, B_63)))), inference(resolution, [status(thm)], [c_78, c_538])).
% 3.46/1.57  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.57  tff(c_891, plain, (![A_79, B_80, B_81]: (r1_tarski(A_79, k2_xboole_0(k2_xboole_0(A_79, B_80), B_81)))), inference(resolution, [status(thm)], [c_563, c_8])).
% 3.46/1.57  tff(c_929, plain, (![A_79, A_1, B_80]: (r1_tarski(A_79, k2_xboole_0(A_1, k2_xboole_0(A_79, B_80))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_891])).
% 3.46/1.57  tff(c_1172, plain, (![A_1]: (r1_tarski('#skF_1', k2_xboole_0(A_1, k4_xboole_0('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1162, c_929])).
% 3.46/1.57  tff(c_1857, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1847, c_1172])).
% 3.46/1.57  tff(c_1958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_1857])).
% 3.46/1.57  tff(c_1959, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 3.46/1.57  tff(c_26, plain, (![A_24, B_25]: (r1_xboole_0(k4_xboole_0(A_24, B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.46/1.57  tff(c_2421, plain, (![A_145, C_146, B_147]: (r1_xboole_0(A_145, C_146) | ~r1_xboole_0(B_147, C_146) | ~r1_tarski(A_145, B_147))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.46/1.57  tff(c_2924, plain, (![A_164, B_165, A_166]: (r1_xboole_0(A_164, B_165) | ~r1_tarski(A_164, k4_xboole_0(A_166, B_165)))), inference(resolution, [status(thm)], [c_26, c_2421])).
% 3.46/1.57  tff(c_2956, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_2924])).
% 3.46/1.57  tff(c_2974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1959, c_2956])).
% 3.46/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.57  
% 3.46/1.57  Inference rules
% 3.46/1.57  ----------------------
% 3.46/1.57  #Ref     : 0
% 3.46/1.57  #Sup     : 729
% 3.46/1.57  #Fact    : 0
% 3.46/1.57  #Define  : 0
% 3.46/1.57  #Split   : 1
% 3.46/1.57  #Chain   : 0
% 3.46/1.57  #Close   : 0
% 3.46/1.57  
% 3.46/1.57  Ordering : KBO
% 3.46/1.57  
% 3.46/1.57  Simplification rules
% 3.46/1.57  ----------------------
% 3.46/1.57  #Subsume      : 19
% 3.46/1.57  #Demod        : 459
% 3.46/1.57  #Tautology    : 523
% 3.46/1.57  #SimpNegUnit  : 2
% 3.46/1.57  #BackRed      : 2
% 3.46/1.57  
% 3.46/1.57  #Partial instantiations: 0
% 3.46/1.57  #Strategies tried      : 1
% 3.46/1.57  
% 3.46/1.57  Timing (in seconds)
% 3.46/1.57  ----------------------
% 3.46/1.57  Preprocessing        : 0.27
% 3.46/1.57  Parsing              : 0.15
% 3.46/1.57  CNF conversion       : 0.02
% 3.46/1.57  Main loop            : 0.55
% 3.46/1.57  Inferencing          : 0.19
% 3.46/1.57  Reduction            : 0.22
% 3.46/1.57  Demodulation         : 0.17
% 3.46/1.57  BG Simplification    : 0.02
% 3.46/1.57  Subsumption          : 0.08
% 3.46/1.57  Abstraction          : 0.02
% 3.46/1.57  MUC search           : 0.00
% 3.46/1.57  Cooper               : 0.00
% 3.46/1.57  Total                : 0.84
% 3.46/1.57  Index Insertion      : 0.00
% 3.46/1.57  Index Deletion       : 0.00
% 3.46/1.57  Index Matching       : 0.00
% 3.46/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
