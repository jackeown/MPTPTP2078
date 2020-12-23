%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:20 EST 2020

% Result     : Theorem 10.16s
% Output     : CNFRefutation 10.24s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 168 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :   66 ( 162 expanded)
%              Number of equality atoms :   58 ( 151 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_99,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_107,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_28])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_129,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_108])).

tff(c_133,plain,(
    ! [A_41] : k4_xboole_0(A_41,A_41) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_129])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,(
    ! [A_41] : k4_xboole_0(A_41,k1_xboole_0) = k3_xboole_0(A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_20])).

tff(c_156,plain,(
    ! [A_41] : k3_xboole_0(A_41,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_138])).

tff(c_346,plain,(
    ! [A_53,B_54,C_55] : k4_xboole_0(k3_xboole_0(A_53,B_54),C_55) = k3_xboole_0(A_53,k4_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_382,plain,(
    ! [A_41,C_55] : k3_xboole_0(A_41,k4_xboole_0(A_41,C_55)) = k4_xboole_0(A_41,C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_346])).

tff(c_123,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,k4_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_108])).

tff(c_5031,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_123])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_242,plain,(
    ! [A_49,B_50] : k2_xboole_0(k3_xboole_0(A_49,B_50),k4_xboole_0(A_49,B_50)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_263,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_5,k1_xboole_0)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_242])).

tff(c_271,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_263])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_85,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_957,plain,(
    ! [A_69,B_70,C_71] : k2_xboole_0(k4_xboole_0(A_69,B_70),k3_xboole_0(A_69,C_71)) = k4_xboole_0(A_69,k4_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1011,plain,(
    ! [A_16,B_17,C_71] : k4_xboole_0(A_16,k4_xboole_0(k4_xboole_0(A_16,B_17),C_71)) = k2_xboole_0(k3_xboole_0(A_16,B_17),k3_xboole_0(A_16,C_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_957])).

tff(c_20734,plain,(
    ! [A_257,B_258,C_259] : k2_xboole_0(k3_xboole_0(A_257,B_258),k3_xboole_0(A_257,C_259)) = k3_xboole_0(A_257,k2_xboole_0(B_258,C_259)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_1011])).

tff(c_21072,plain,(
    ! [B_258] : k3_xboole_0('#skF_1',k2_xboole_0(B_258,k4_xboole_0('#skF_2','#skF_3'))) = k2_xboole_0(k3_xboole_0('#skF_1',B_258),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_20734])).

tff(c_24257,plain,(
    ! [B_280] : k3_xboole_0('#skF_1',k2_xboole_0(B_280,k4_xboole_0('#skF_2','#skF_3'))) = k3_xboole_0('#skF_1',B_280) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_2,c_21072])).

tff(c_24442,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_24257])).

tff(c_24771,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_3')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24442,c_5031])).

tff(c_24819,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5031,c_24771])).

tff(c_132,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_129])).

tff(c_273,plain,(
    ! [A_51] : k2_xboole_0(k1_xboole_0,A_51) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_263])).

tff(c_301,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_273])).

tff(c_24,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_511,plain,(
    ! [A_58,B_59,C_60] : k4_xboole_0(k4_xboole_0(A_58,B_59),C_60) = k4_xboole_0(A_58,k2_xboole_0(B_59,C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_563,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k2_xboole_0(B_59,k4_xboole_0(A_58,B_59))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_511])).

tff(c_623,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k2_xboole_0(B_63,A_62)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_563])).

tff(c_867,plain,(
    ! [A_67,B_68] : k4_xboole_0(k4_xboole_0(A_67,B_68),A_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_623])).

tff(c_884,plain,(
    ! [A_67,B_68] : k2_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = k2_xboole_0(A_67,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_14])).

tff(c_942,plain,(
    ! [A_67,B_68] : k2_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_884])).

tff(c_648,plain,(
    ! [A_62,B_63] : k3_xboole_0(A_62,k2_xboole_0(B_63,A_62)) = k4_xboole_0(A_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_20])).

tff(c_696,plain,(
    ! [A_62,B_63] : k3_xboole_0(A_62,k2_xboole_0(B_63,A_62)) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_648])).

tff(c_9269,plain,(
    ! [A_179,C_180,B_181] : k2_xboole_0(k3_xboole_0(A_179,C_180),k4_xboole_0(A_179,B_181)) = k4_xboole_0(A_179,k4_xboole_0(B_181,C_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_2])).

tff(c_9472,plain,(
    ! [A_62,B_181,B_63] : k4_xboole_0(A_62,k4_xboole_0(B_181,k2_xboole_0(B_63,A_62))) = k2_xboole_0(A_62,k4_xboole_0(A_62,B_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_9269])).

tff(c_9601,plain,(
    ! [A_182,B_183,B_184] : k4_xboole_0(A_182,k4_xboole_0(B_183,k2_xboole_0(B_184,A_182))) = A_182 ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_9472])).

tff(c_9688,plain,(
    ! [A_182,B_183,B_184] : k3_xboole_0(A_182,k4_xboole_0(B_183,k2_xboole_0(B_184,A_182))) = k4_xboole_0(A_182,A_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_9601,c_20])).

tff(c_9854,plain,(
    ! [A_182,B_183,B_184] : k3_xboole_0(A_182,k4_xboole_0(B_183,k2_xboole_0(B_184,A_182))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_9688])).

tff(c_26946,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24819,c_9854])).

tff(c_27060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_26946])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:52:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.16/4.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.16/4.22  
% 10.16/4.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.16/4.22  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.16/4.22  
% 10.16/4.22  %Foreground sorts:
% 10.16/4.22  
% 10.16/4.22  
% 10.16/4.22  %Background operators:
% 10.16/4.22  
% 10.16/4.22  
% 10.16/4.22  %Foreground operators:
% 10.16/4.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.16/4.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.16/4.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.16/4.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.16/4.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.16/4.22  tff('#skF_2', type, '#skF_2': $i).
% 10.16/4.22  tff('#skF_3', type, '#skF_3': $i).
% 10.16/4.22  tff('#skF_1', type, '#skF_1': $i).
% 10.16/4.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.16/4.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.16/4.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.16/4.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.16/4.22  
% 10.24/4.24  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.24/4.24  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 10.24/4.24  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.24/4.24  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.24/4.24  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.24/4.24  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 10.24/4.24  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.24/4.24  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 10.24/4.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.24/4.24  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.24/4.24  tff(f_53, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 10.24/4.24  tff(c_99, plain, (![A_37, B_38]: (r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.24/4.24  tff(c_28, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.24/4.24  tff(c_107, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_28])).
% 10.24/4.24  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.24/4.24  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.24/4.24  tff(c_108, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.24/4.24  tff(c_129, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_108])).
% 10.24/4.24  tff(c_133, plain, (![A_41]: (k4_xboole_0(A_41, A_41)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_129])).
% 10.24/4.24  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.24/4.24  tff(c_138, plain, (![A_41]: (k4_xboole_0(A_41, k1_xboole_0)=k3_xboole_0(A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_133, c_20])).
% 10.24/4.24  tff(c_156, plain, (![A_41]: (k3_xboole_0(A_41, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_138])).
% 10.24/4.24  tff(c_346, plain, (![A_53, B_54, C_55]: (k4_xboole_0(k3_xboole_0(A_53, B_54), C_55)=k3_xboole_0(A_53, k4_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.24/4.24  tff(c_382, plain, (![A_41, C_55]: (k3_xboole_0(A_41, k4_xboole_0(A_41, C_55))=k4_xboole_0(A_41, C_55))), inference(superposition, [status(thm), theory('equality')], [c_156, c_346])).
% 10.24/4.24  tff(c_123, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k3_xboole_0(A_16, k4_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_108])).
% 10.24/4.24  tff(c_5031, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_123])).
% 10.24/4.24  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.24/4.24  tff(c_242, plain, (![A_49, B_50]: (k2_xboole_0(k3_xboole_0(A_49, B_50), k4_xboole_0(A_49, B_50))=A_49)), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.24/4.24  tff(c_263, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_5, k1_xboole_0))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_242])).
% 10.24/4.24  tff(c_271, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_263])).
% 10.24/4.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.24/4.24  tff(c_30, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.24/4.24  tff(c_85, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.24/4.24  tff(c_89, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_85])).
% 10.24/4.24  tff(c_18, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.24/4.24  tff(c_957, plain, (![A_69, B_70, C_71]: (k2_xboole_0(k4_xboole_0(A_69, B_70), k3_xboole_0(A_69, C_71))=k4_xboole_0(A_69, k4_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.24/4.24  tff(c_1011, plain, (![A_16, B_17, C_71]: (k4_xboole_0(A_16, k4_xboole_0(k4_xboole_0(A_16, B_17), C_71))=k2_xboole_0(k3_xboole_0(A_16, B_17), k3_xboole_0(A_16, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_957])).
% 10.24/4.24  tff(c_20734, plain, (![A_257, B_258, C_259]: (k2_xboole_0(k3_xboole_0(A_257, B_258), k3_xboole_0(A_257, C_259))=k3_xboole_0(A_257, k2_xboole_0(B_258, C_259)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_1011])).
% 10.24/4.24  tff(c_21072, plain, (![B_258]: (k3_xboole_0('#skF_1', k2_xboole_0(B_258, k4_xboole_0('#skF_2', '#skF_3')))=k2_xboole_0(k3_xboole_0('#skF_1', B_258), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_89, c_20734])).
% 10.24/4.24  tff(c_24257, plain, (![B_280]: (k3_xboole_0('#skF_1', k2_xboole_0(B_280, k4_xboole_0('#skF_2', '#skF_3')))=k3_xboole_0('#skF_1', B_280))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_2, c_21072])).
% 10.24/4.24  tff(c_24442, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_24257])).
% 10.24/4.24  tff(c_24771, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24442, c_5031])).
% 10.24/4.24  tff(c_24819, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5031, c_24771])).
% 10.24/4.24  tff(c_132, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_129])).
% 10.24/4.24  tff(c_273, plain, (![A_51]: (k2_xboole_0(k1_xboole_0, A_51)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_263])).
% 10.24/4.24  tff(c_301, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_273])).
% 10.24/4.24  tff(c_24, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.24/4.24  tff(c_511, plain, (![A_58, B_59, C_60]: (k4_xboole_0(k4_xboole_0(A_58, B_59), C_60)=k4_xboole_0(A_58, k2_xboole_0(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.24/4.24  tff(c_563, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k2_xboole_0(B_59, k4_xboole_0(A_58, B_59)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_132, c_511])).
% 10.24/4.24  tff(c_623, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k2_xboole_0(B_63, A_62))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_563])).
% 10.24/4.24  tff(c_867, plain, (![A_67, B_68]: (k4_xboole_0(k4_xboole_0(A_67, B_68), A_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_623])).
% 10.24/4.24  tff(c_884, plain, (![A_67, B_68]: (k2_xboole_0(A_67, k4_xboole_0(A_67, B_68))=k2_xboole_0(A_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_867, c_14])).
% 10.24/4.24  tff(c_942, plain, (![A_67, B_68]: (k2_xboole_0(A_67, k4_xboole_0(A_67, B_68))=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_884])).
% 10.24/4.24  tff(c_648, plain, (![A_62, B_63]: (k3_xboole_0(A_62, k2_xboole_0(B_63, A_62))=k4_xboole_0(A_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_623, c_20])).
% 10.24/4.24  tff(c_696, plain, (![A_62, B_63]: (k3_xboole_0(A_62, k2_xboole_0(B_63, A_62))=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_648])).
% 10.24/4.24  tff(c_9269, plain, (![A_179, C_180, B_181]: (k2_xboole_0(k3_xboole_0(A_179, C_180), k4_xboole_0(A_179, B_181))=k4_xboole_0(A_179, k4_xboole_0(B_181, C_180)))), inference(superposition, [status(thm), theory('equality')], [c_957, c_2])).
% 10.24/4.24  tff(c_9472, plain, (![A_62, B_181, B_63]: (k4_xboole_0(A_62, k4_xboole_0(B_181, k2_xboole_0(B_63, A_62)))=k2_xboole_0(A_62, k4_xboole_0(A_62, B_181)))), inference(superposition, [status(thm), theory('equality')], [c_696, c_9269])).
% 10.24/4.24  tff(c_9601, plain, (![A_182, B_183, B_184]: (k4_xboole_0(A_182, k4_xboole_0(B_183, k2_xboole_0(B_184, A_182)))=A_182)), inference(demodulation, [status(thm), theory('equality')], [c_942, c_9472])).
% 10.24/4.24  tff(c_9688, plain, (![A_182, B_183, B_184]: (k3_xboole_0(A_182, k4_xboole_0(B_183, k2_xboole_0(B_184, A_182)))=k4_xboole_0(A_182, A_182))), inference(superposition, [status(thm), theory('equality')], [c_9601, c_20])).
% 10.24/4.24  tff(c_9854, plain, (![A_182, B_183, B_184]: (k3_xboole_0(A_182, k4_xboole_0(B_183, k2_xboole_0(B_184, A_182)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_132, c_9688])).
% 10.24/4.24  tff(c_26946, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24819, c_9854])).
% 10.24/4.24  tff(c_27060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_26946])).
% 10.24/4.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.24/4.24  
% 10.24/4.24  Inference rules
% 10.24/4.24  ----------------------
% 10.24/4.24  #Ref     : 0
% 10.24/4.24  #Sup     : 6806
% 10.24/4.24  #Fact    : 0
% 10.24/4.24  #Define  : 0
% 10.24/4.24  #Split   : 3
% 10.24/4.24  #Chain   : 0
% 10.24/4.24  #Close   : 0
% 10.24/4.24  
% 10.24/4.24  Ordering : KBO
% 10.24/4.24  
% 10.24/4.24  Simplification rules
% 10.24/4.24  ----------------------
% 10.24/4.24  #Subsume      : 207
% 10.24/4.24  #Demod        : 7258
% 10.24/4.24  #Tautology    : 4586
% 10.24/4.24  #SimpNegUnit  : 1
% 10.24/4.24  #BackRed      : 1
% 10.24/4.24  
% 10.24/4.24  #Partial instantiations: 0
% 10.24/4.24  #Strategies tried      : 1
% 10.24/4.24  
% 10.24/4.24  Timing (in seconds)
% 10.24/4.24  ----------------------
% 10.24/4.24  Preprocessing        : 0.30
% 10.24/4.24  Parsing              : 0.16
% 10.24/4.24  CNF conversion       : 0.02
% 10.24/4.24  Main loop            : 3.13
% 10.24/4.24  Inferencing          : 0.63
% 10.24/4.24  Reduction            : 1.79
% 10.24/4.24  Demodulation         : 1.58
% 10.24/4.24  BG Simplification    : 0.08
% 10.24/4.24  Subsumption          : 0.49
% 10.24/4.24  Abstraction          : 0.12
% 10.24/4.24  MUC search           : 0.00
% 10.24/4.24  Cooper               : 0.00
% 10.24/4.24  Total                : 3.47
% 10.24/4.24  Index Insertion      : 0.00
% 10.24/4.25  Index Deletion       : 0.00
% 10.24/4.25  Index Matching       : 0.00
% 10.24/4.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
