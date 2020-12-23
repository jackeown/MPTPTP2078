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
% DateTime   : Thu Dec  3 09:43:18 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 146 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 154 expanded)
%              Number of equality atoms :   58 ( 123 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(c_253,plain,(
    ! [A_31,B_32] :
      ( r1_xboole_0(A_31,B_32)
      | k3_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_257,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_253,c_26])).

tff(c_14,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_269,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_277,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_269])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_281,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_4])).

tff(c_370,plain,(
    ! [A_41,B_42] : k2_xboole_0(k3_xboole_0(A_41,B_42),k4_xboole_0(A_41,B_42)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_388,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_370])).

tff(c_155,plain,(
    ! [B_28,A_29] : k2_xboole_0(B_28,A_29) = k2_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_171,plain,(
    ! [A_29] : k2_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_14])).

tff(c_582,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_171])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_75,plain,(
    ! [B_25,A_26] : k3_xboole_0(B_25,A_26) = k3_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_26] : k3_xboole_0(k1_xboole_0,A_26) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_16])).

tff(c_438,plain,(
    ! [A_43] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,A_43)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_370])).

tff(c_443,plain,(
    ! [A_43] : k4_xboole_0(k1_xboole_0,A_43) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_171])).

tff(c_18,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_299,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_314,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_299])).

tff(c_317,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_314])).

tff(c_465,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k4_xboole_0(A_44,B_45),C_46) = k4_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_501,plain,(
    ! [A_13,C_46] : k4_xboole_0(A_13,k2_xboole_0(A_13,C_46)) = k4_xboole_0(k1_xboole_0,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_465])).

tff(c_1082,plain,(
    ! [A_57,C_58] : k4_xboole_0(A_57,k2_xboole_0(A_57,C_58)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_501])).

tff(c_1145,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1082])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_260,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_264,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_260])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k4_xboole_0(A_14,B_15),C_16) = k4_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_512,plain,(
    ! [A_44,B_45,B_18] : k4_xboole_0(A_44,k2_xboole_0(B_45,k4_xboole_0(k4_xboole_0(A_44,B_45),B_18))) = k3_xboole_0(k4_xboole_0(A_44,B_45),B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_465])).

tff(c_2722,plain,(
    ! [A_84,B_85,B_86] : k4_xboole_0(A_84,k2_xboole_0(B_85,k4_xboole_0(A_84,k2_xboole_0(B_85,B_86)))) = k3_xboole_0(k4_xboole_0(A_84,B_85),B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_512])).

tff(c_2878,plain,(
    ! [A_84] : k4_xboole_0(A_84,k2_xboole_0('#skF_1',k4_xboole_0(A_84,'#skF_2'))) = k3_xboole_0(k4_xboole_0(A_84,'#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_2722])).

tff(c_3068,plain,(
    ! [A_89] : k4_xboole_0(A_89,k2_xboole_0('#skF_1',k4_xboole_0(A_89,'#skF_2'))) = k3_xboole_0('#skF_2',k4_xboole_0(A_89,'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2878])).

tff(c_3150,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_3')) = k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_3068])).

tff(c_3185,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_3150])).

tff(c_24,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_xboole_0(A_19,B_20),k4_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2154,plain,(
    ! [A_77,B_78,C_79] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_77,B_78),C_79),k4_xboole_0(A_77,k2_xboole_0(B_78,C_79))) = k4_xboole_0(A_77,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_24])).

tff(c_2304,plain,(
    ! [A_77] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_77,'#skF_1'),'#skF_2'),k4_xboole_0(A_77,'#skF_2')) = k4_xboole_0(A_77,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_2154])).

tff(c_2375,plain,(
    ! [A_77] : k2_xboole_0(k4_xboole_0(A_77,'#skF_2'),k3_xboole_0('#skF_2',k4_xboole_0(A_77,'#skF_1'))) = k4_xboole_0(A_77,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4,c_2304])).

tff(c_3194,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_2'),k1_xboole_0) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3185,c_2375])).

tff(c_3215,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_582,c_3194])).

tff(c_478,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k2_xboole_0(B_45,k4_xboole_0(A_44,B_45))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_317])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2894,plain,(
    ! [A_84,A_7] : k4_xboole_0(A_84,k2_xboole_0(A_7,k4_xboole_0(A_84,A_7))) = k3_xboole_0(k4_xboole_0(A_84,A_7),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2722])).

tff(c_2932,plain,(
    ! [A_7,A_84] : k3_xboole_0(A_7,k4_xboole_0(A_84,A_7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_4,c_2894])).

tff(c_3226,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3215,c_2932])).

tff(c_3260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_3226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:06:45 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.87  
% 4.09/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.88  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.09/1.88  
% 4.09/1.88  %Foreground sorts:
% 4.09/1.88  
% 4.09/1.88  
% 4.09/1.88  %Background operators:
% 4.09/1.88  
% 4.09/1.88  
% 4.09/1.88  %Foreground operators:
% 4.09/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.09/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.09/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.09/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.09/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.09/1.88  
% 4.09/1.89  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.09/1.89  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.09/1.89  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.09/1.89  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.09/1.89  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.09/1.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.09/1.89  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.09/1.89  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.09/1.89  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.09/1.89  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.09/1.89  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.09/1.89  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.09/1.89  tff(c_253, plain, (![A_31, B_32]: (r1_xboole_0(A_31, B_32) | k3_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.09/1.89  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.09/1.89  tff(c_257, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_253, c_26])).
% 4.09/1.89  tff(c_14, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.09/1.89  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.09/1.89  tff(c_269, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.09/1.89  tff(c_277, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_269])).
% 4.09/1.89  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.09/1.89  tff(c_281, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_277, c_4])).
% 4.09/1.89  tff(c_370, plain, (![A_41, B_42]: (k2_xboole_0(k3_xboole_0(A_41, B_42), k4_xboole_0(A_41, B_42))=A_41)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.89  tff(c_388, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_281, c_370])).
% 4.09/1.89  tff(c_155, plain, (![B_28, A_29]: (k2_xboole_0(B_28, A_29)=k2_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.09/1.89  tff(c_171, plain, (![A_29]: (k2_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_155, c_14])).
% 4.09/1.89  tff(c_582, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_388, c_171])).
% 4.09/1.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.09/1.89  tff(c_75, plain, (![B_25, A_26]: (k3_xboole_0(B_25, A_26)=k3_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.09/1.89  tff(c_16, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.09/1.89  tff(c_91, plain, (![A_26]: (k3_xboole_0(k1_xboole_0, A_26)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75, c_16])).
% 4.09/1.89  tff(c_438, plain, (![A_43]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, A_43))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_91, c_370])).
% 4.09/1.89  tff(c_443, plain, (![A_43]: (k4_xboole_0(k1_xboole_0, A_43)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_438, c_171])).
% 4.09/1.89  tff(c_18, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.09/1.89  tff(c_299, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.09/1.89  tff(c_314, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_299])).
% 4.09/1.89  tff(c_317, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_314])).
% 4.09/1.89  tff(c_465, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), C_46)=k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.09/1.89  tff(c_501, plain, (![A_13, C_46]: (k4_xboole_0(A_13, k2_xboole_0(A_13, C_46))=k4_xboole_0(k1_xboole_0, C_46))), inference(superposition, [status(thm), theory('equality')], [c_317, c_465])).
% 4.09/1.89  tff(c_1082, plain, (![A_57, C_58]: (k4_xboole_0(A_57, k2_xboole_0(A_57, C_58))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_443, c_501])).
% 4.09/1.89  tff(c_1145, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1082])).
% 4.09/1.89  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.09/1.89  tff(c_260, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.09/1.89  tff(c_264, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_30, c_260])).
% 4.09/1.89  tff(c_20, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k4_xboole_0(A_14, B_15), C_16)=k4_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.09/1.89  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.09/1.89  tff(c_512, plain, (![A_44, B_45, B_18]: (k4_xboole_0(A_44, k2_xboole_0(B_45, k4_xboole_0(k4_xboole_0(A_44, B_45), B_18)))=k3_xboole_0(k4_xboole_0(A_44, B_45), B_18))), inference(superposition, [status(thm), theory('equality')], [c_22, c_465])).
% 4.09/1.89  tff(c_2722, plain, (![A_84, B_85, B_86]: (k4_xboole_0(A_84, k2_xboole_0(B_85, k4_xboole_0(A_84, k2_xboole_0(B_85, B_86))))=k3_xboole_0(k4_xboole_0(A_84, B_85), B_86))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_512])).
% 4.09/1.89  tff(c_2878, plain, (![A_84]: (k4_xboole_0(A_84, k2_xboole_0('#skF_1', k4_xboole_0(A_84, '#skF_2')))=k3_xboole_0(k4_xboole_0(A_84, '#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_264, c_2722])).
% 4.09/1.89  tff(c_3068, plain, (![A_89]: (k4_xboole_0(A_89, k2_xboole_0('#skF_1', k4_xboole_0(A_89, '#skF_2')))=k3_xboole_0('#skF_2', k4_xboole_0(A_89, '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2878])).
% 4.09/1.89  tff(c_3150, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_3'))=k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_582, c_3068])).
% 4.09/1.89  tff(c_3185, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1145, c_3150])).
% 4.09/1.89  tff(c_24, plain, (![A_19, B_20]: (k2_xboole_0(k3_xboole_0(A_19, B_20), k4_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.89  tff(c_2154, plain, (![A_77, B_78, C_79]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_77, B_78), C_79), k4_xboole_0(A_77, k2_xboole_0(B_78, C_79)))=k4_xboole_0(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_465, c_24])).
% 4.09/1.89  tff(c_2304, plain, (![A_77]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_77, '#skF_1'), '#skF_2'), k4_xboole_0(A_77, '#skF_2'))=k4_xboole_0(A_77, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_264, c_2154])).
% 4.09/1.89  tff(c_2375, plain, (![A_77]: (k2_xboole_0(k4_xboole_0(A_77, '#skF_2'), k3_xboole_0('#skF_2', k4_xboole_0(A_77, '#skF_1')))=k4_xboole_0(A_77, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4, c_2304])).
% 4.09/1.89  tff(c_3194, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_2'), k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3185, c_2375])).
% 4.09/1.89  tff(c_3215, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_582, c_3194])).
% 4.09/1.89  tff(c_478, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k2_xboole_0(B_45, k4_xboole_0(A_44, B_45)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_465, c_317])).
% 4.09/1.89  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.09/1.89  tff(c_2894, plain, (![A_84, A_7]: (k4_xboole_0(A_84, k2_xboole_0(A_7, k4_xboole_0(A_84, A_7)))=k3_xboole_0(k4_xboole_0(A_84, A_7), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2722])).
% 4.09/1.89  tff(c_2932, plain, (![A_7, A_84]: (k3_xboole_0(A_7, k4_xboole_0(A_84, A_7))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_478, c_4, c_2894])).
% 4.09/1.89  tff(c_3226, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3215, c_2932])).
% 4.09/1.89  tff(c_3260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_3226])).
% 4.09/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.89  
% 4.09/1.89  Inference rules
% 4.09/1.89  ----------------------
% 4.09/1.89  #Ref     : 0
% 4.09/1.89  #Sup     : 815
% 4.09/1.89  #Fact    : 0
% 4.09/1.89  #Define  : 0
% 4.09/1.89  #Split   : 0
% 4.09/1.89  #Chain   : 0
% 4.09/1.89  #Close   : 0
% 4.09/1.89  
% 4.09/1.89  Ordering : KBO
% 4.09/1.89  
% 4.09/1.89  Simplification rules
% 4.09/1.89  ----------------------
% 4.09/1.89  #Subsume      : 0
% 4.09/1.89  #Demod        : 852
% 4.09/1.89  #Tautology    : 521
% 4.09/1.89  #SimpNegUnit  : 1
% 4.09/1.89  #BackRed      : 4
% 4.09/1.89  
% 4.09/1.89  #Partial instantiations: 0
% 4.09/1.89  #Strategies tried      : 1
% 4.09/1.89  
% 4.09/1.89  Timing (in seconds)
% 4.09/1.89  ----------------------
% 4.09/1.90  Preprocessing        : 0.29
% 4.09/1.90  Parsing              : 0.16
% 4.09/1.90  CNF conversion       : 0.02
% 4.09/1.90  Main loop            : 0.77
% 4.09/1.90  Inferencing          : 0.22
% 4.09/1.90  Reduction            : 0.39
% 4.09/1.90  Demodulation         : 0.33
% 4.09/1.90  BG Simplification    : 0.03
% 4.09/1.90  Subsumption          : 0.09
% 4.09/1.90  Abstraction          : 0.04
% 4.09/1.90  MUC search           : 0.00
% 4.09/1.90  Cooper               : 0.00
% 4.09/1.90  Total                : 1.10
% 4.09/1.90  Index Insertion      : 0.00
% 4.09/1.90  Index Deletion       : 0.00
% 4.09/1.90  Index Matching       : 0.00
% 4.40/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
