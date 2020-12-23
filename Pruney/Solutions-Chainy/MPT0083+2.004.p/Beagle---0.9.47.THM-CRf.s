%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:01 EST 2020

% Result     : Theorem 20.77s
% Output     : CNFRefutation 20.77s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 117 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 113 expanded)
%              Number of equality atoms :   56 (  96 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_184,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_184])).

tff(c_421,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1841,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k3_xboole_0(B_96,A_95)) = k4_xboole_0(A_95,B_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_421])).

tff(c_1904,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_1841])).

tff(c_1934,plain,(
    k4_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1904])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_531,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_550,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,k4_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_531])).

tff(c_2855,plain,(
    ! [A_107,B_108] : k3_xboole_0(A_107,k4_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_550])).

tff(c_26,plain,(
    ! [A_20,B_21] : k2_xboole_0(k3_xboole_0(A_20,B_21),k4_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_427,plain,(
    ! [A_53,B_54] : k2_xboole_0(k3_xboole_0(A_53,B_54),k4_xboole_0(A_53,B_54)) = k2_xboole_0(k3_xboole_0(A_53,B_54),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_16])).

tff(c_458,plain,(
    ! [A_53,B_54] : k2_xboole_0(k3_xboole_0(A_53,B_54),A_53) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_427])).

tff(c_2884,plain,(
    ! [A_107,B_108] : k2_xboole_0(k4_xboole_0(A_107,B_108),A_107) = A_107 ),
    inference(superposition,[status(thm),theory(equality)],[c_2855,c_458])).

tff(c_556,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,k3_xboole_0(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_531])).

tff(c_581,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_556])).

tff(c_1150,plain,(
    ! [A_78,B_79,C_80] : k2_xboole_0(k4_xboole_0(A_78,B_79),k3_xboole_0(A_78,C_80)) = k4_xboole_0(A_78,k4_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12173,plain,(
    ! [A_189,B_190,B_191] : k2_xboole_0(k4_xboole_0(A_189,B_190),k3_xboole_0(B_191,A_189)) = k4_xboole_0(A_189,k4_xboole_0(B_190,B_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1150])).

tff(c_12325,plain,(
    ! [A_16,B_17,B_190] : k2_xboole_0(k4_xboole_0(k3_xboole_0(A_16,B_17),B_190),k3_xboole_0(A_16,B_17)) = k4_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(B_190,A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_12173])).

tff(c_40636,plain,(
    ! [A_396,B_397,B_398] : k4_xboole_0(k3_xboole_0(A_396,B_397),k4_xboole_0(B_398,A_396)) = k3_xboole_0(A_396,B_397) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2884,c_12325])).

tff(c_41244,plain,(
    ! [B_399] : k4_xboole_0(k3_xboole_0('#skF_1',B_399),'#skF_2') = k3_xboole_0('#skF_1',B_399) ),
    inference(superposition,[status(thm),theory(equality)],[c_1934,c_40636])).

tff(c_42558,plain,(
    ! [A_403] : k4_xboole_0(k3_xboole_0(A_403,'#skF_1'),'#skF_2') = k3_xboole_0('#skF_1',A_403) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_41244])).

tff(c_757,plain,(
    ! [A_66,B_67,C_68] : k4_xboole_0(k4_xboole_0(A_66,B_67),C_68) = k4_xboole_0(A_66,k2_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_575,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_531])).

tff(c_587,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_575])).

tff(c_767,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k2_xboole_0(B_67,k4_xboole_0(A_66,B_67))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_587])).

tff(c_837,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k2_xboole_0(B_67,A_66)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_767])).

tff(c_50,plain,(
    ! [A_27,B_28] : r1_tarski(k3_xboole_0(A_27,B_28),A_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_50])).

tff(c_167,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_182,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_167])).

tff(c_1225,plain,(
    ! [A_12,C_80] : k4_xboole_0(A_12,k4_xboole_0(k1_xboole_0,C_80)) = k2_xboole_0(A_12,k3_xboole_0(A_12,C_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1150])).

tff(c_1241,plain,(
    ! [A_12,C_80] : k2_xboole_0(A_12,k3_xboole_0(A_12,C_80)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_182,c_1225])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_774,plain,(
    ! [A_66,B_67,B_19] : k4_xboole_0(A_66,k2_xboole_0(B_67,k4_xboole_0(k4_xboole_0(A_66,B_67),B_19))) = k3_xboole_0(k4_xboole_0(A_66,B_67),B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_24])).

tff(c_23338,plain,(
    ! [A_300,B_301,B_302] : k4_xboole_0(A_300,k2_xboole_0(B_301,k4_xboole_0(A_300,k2_xboole_0(B_301,B_302)))) = k3_xboole_0(k4_xboole_0(A_300,B_301),B_302) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_774])).

tff(c_23704,plain,(
    ! [A_300,A_12,C_80] : k4_xboole_0(A_300,k2_xboole_0(A_12,k4_xboole_0(A_300,A_12))) = k3_xboole_0(k4_xboole_0(A_300,A_12),k3_xboole_0(A_12,C_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_23338])).

tff(c_24841,plain,(
    ! [A_310,A_311,C_312] : k3_xboole_0(k4_xboole_0(A_310,A_311),k3_xboole_0(A_311,C_312)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_16,c_23704])).

tff(c_25261,plain,(
    ! [A_310,B_2,A_1] : k3_xboole_0(k4_xboole_0(A_310,B_2),k3_xboole_0(A_1,B_2)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_24841])).

tff(c_42599,plain,(
    ! [A_403,A_1] : k3_xboole_0(k3_xboole_0('#skF_1',A_403),k3_xboole_0(A_1,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42558,c_25261])).

tff(c_253,plain,(
    ! [A_44,B_45] :
      ( r1_xboole_0(A_44,B_45)
      | k3_xboole_0(A_44,B_45) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_261,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_253,c_33])).

tff(c_107101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42599,c_261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:43:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.77/13.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.77/13.23  
% 20.77/13.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.77/13.23  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 20.77/13.23  
% 20.77/13.23  %Foreground sorts:
% 20.77/13.23  
% 20.77/13.23  
% 20.77/13.23  %Background operators:
% 20.77/13.23  
% 20.77/13.23  
% 20.77/13.23  %Foreground operators:
% 20.77/13.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.77/13.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.77/13.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.77/13.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.77/13.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 20.77/13.23  tff('#skF_2', type, '#skF_2': $i).
% 20.77/13.23  tff('#skF_3', type, '#skF_3': $i).
% 20.77/13.23  tff('#skF_1', type, '#skF_1': $i).
% 20.77/13.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.77/13.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.77/13.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.77/13.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.77/13.23  
% 20.77/13.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 20.77/13.25  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 20.77/13.25  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 20.77/13.25  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 20.77/13.25  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 20.77/13.25  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 20.77/13.25  tff(f_51, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 20.77/13.25  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 20.77/13.25  tff(f_53, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 20.77/13.25  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 20.77/13.25  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 20.77/13.25  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 20.77/13.25  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 20.77/13.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.77/13.25  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.77/13.25  tff(c_32, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.77/13.25  tff(c_184, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.77/13.25  tff(c_188, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_184])).
% 20.77/13.25  tff(c_421, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.77/13.25  tff(c_1841, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k3_xboole_0(B_96, A_95))=k4_xboole_0(A_95, B_96))), inference(superposition, [status(thm), theory('equality')], [c_2, c_421])).
% 20.77/13.25  tff(c_1904, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_188, c_1841])).
% 20.77/13.25  tff(c_1934, plain, (k4_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1904])).
% 20.77/13.25  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.77/13.25  tff(c_24, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.77/13.25  tff(c_531, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.77/13.25  tff(c_550, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k3_xboole_0(A_18, k4_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_531])).
% 20.77/13.25  tff(c_2855, plain, (![A_107, B_108]: (k3_xboole_0(A_107, k4_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_550])).
% 20.77/13.25  tff(c_26, plain, (![A_20, B_21]: (k2_xboole_0(k3_xboole_0(A_20, B_21), k4_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_51])).
% 20.77/13.25  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.77/13.25  tff(c_427, plain, (![A_53, B_54]: (k2_xboole_0(k3_xboole_0(A_53, B_54), k4_xboole_0(A_53, B_54))=k2_xboole_0(k3_xboole_0(A_53, B_54), A_53))), inference(superposition, [status(thm), theory('equality')], [c_421, c_16])).
% 20.77/13.25  tff(c_458, plain, (![A_53, B_54]: (k2_xboole_0(k3_xboole_0(A_53, B_54), A_53)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_427])).
% 20.77/13.25  tff(c_2884, plain, (![A_107, B_108]: (k2_xboole_0(k4_xboole_0(A_107, B_108), A_107)=A_107)), inference(superposition, [status(thm), theory('equality')], [c_2855, c_458])).
% 20.77/13.25  tff(c_556, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, k3_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_531])).
% 20.77/13.25  tff(c_581, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_556])).
% 20.77/13.25  tff(c_1150, plain, (![A_78, B_79, C_80]: (k2_xboole_0(k4_xboole_0(A_78, B_79), k3_xboole_0(A_78, C_80))=k4_xboole_0(A_78, k4_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.77/13.25  tff(c_12173, plain, (![A_189, B_190, B_191]: (k2_xboole_0(k4_xboole_0(A_189, B_190), k3_xboole_0(B_191, A_189))=k4_xboole_0(A_189, k4_xboole_0(B_190, B_191)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1150])).
% 20.77/13.25  tff(c_12325, plain, (![A_16, B_17, B_190]: (k2_xboole_0(k4_xboole_0(k3_xboole_0(A_16, B_17), B_190), k3_xboole_0(A_16, B_17))=k4_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(B_190, A_16)))), inference(superposition, [status(thm), theory('equality')], [c_581, c_12173])).
% 20.77/13.25  tff(c_40636, plain, (![A_396, B_397, B_398]: (k4_xboole_0(k3_xboole_0(A_396, B_397), k4_xboole_0(B_398, A_396))=k3_xboole_0(A_396, B_397))), inference(demodulation, [status(thm), theory('equality')], [c_2884, c_12325])).
% 20.77/13.25  tff(c_41244, plain, (![B_399]: (k4_xboole_0(k3_xboole_0('#skF_1', B_399), '#skF_2')=k3_xboole_0('#skF_1', B_399))), inference(superposition, [status(thm), theory('equality')], [c_1934, c_40636])).
% 20.77/13.25  tff(c_42558, plain, (![A_403]: (k4_xboole_0(k3_xboole_0(A_403, '#skF_1'), '#skF_2')=k3_xboole_0('#skF_1', A_403))), inference(superposition, [status(thm), theory('equality')], [c_2, c_41244])).
% 20.77/13.25  tff(c_757, plain, (![A_66, B_67, C_68]: (k4_xboole_0(k4_xboole_0(A_66, B_67), C_68)=k4_xboole_0(A_66, k2_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.77/13.25  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.77/13.25  tff(c_575, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_531])).
% 20.77/13.25  tff(c_587, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_575])).
% 20.77/13.25  tff(c_767, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k2_xboole_0(B_67, k4_xboole_0(A_66, B_67)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_757, c_587])).
% 20.77/13.25  tff(c_837, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k2_xboole_0(B_67, A_66))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_767])).
% 20.77/13.25  tff(c_50, plain, (![A_27, B_28]: (r1_tarski(k3_xboole_0(A_27, B_28), A_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.77/13.25  tff(c_53, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_14, c_50])).
% 20.77/13.25  tff(c_167, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 20.77/13.25  tff(c_182, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_53, c_167])).
% 20.77/13.25  tff(c_1225, plain, (![A_12, C_80]: (k4_xboole_0(A_12, k4_xboole_0(k1_xboole_0, C_80))=k2_xboole_0(A_12, k3_xboole_0(A_12, C_80)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1150])).
% 20.77/13.25  tff(c_1241, plain, (![A_12, C_80]: (k2_xboole_0(A_12, k3_xboole_0(A_12, C_80))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_182, c_1225])).
% 20.77/13.25  tff(c_20, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.77/13.25  tff(c_774, plain, (![A_66, B_67, B_19]: (k4_xboole_0(A_66, k2_xboole_0(B_67, k4_xboole_0(k4_xboole_0(A_66, B_67), B_19)))=k3_xboole_0(k4_xboole_0(A_66, B_67), B_19))), inference(superposition, [status(thm), theory('equality')], [c_757, c_24])).
% 20.77/13.25  tff(c_23338, plain, (![A_300, B_301, B_302]: (k4_xboole_0(A_300, k2_xboole_0(B_301, k4_xboole_0(A_300, k2_xboole_0(B_301, B_302))))=k3_xboole_0(k4_xboole_0(A_300, B_301), B_302))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_774])).
% 20.77/13.25  tff(c_23704, plain, (![A_300, A_12, C_80]: (k4_xboole_0(A_300, k2_xboole_0(A_12, k4_xboole_0(A_300, A_12)))=k3_xboole_0(k4_xboole_0(A_300, A_12), k3_xboole_0(A_12, C_80)))), inference(superposition, [status(thm), theory('equality')], [c_1241, c_23338])).
% 20.77/13.25  tff(c_24841, plain, (![A_310, A_311, C_312]: (k3_xboole_0(k4_xboole_0(A_310, A_311), k3_xboole_0(A_311, C_312))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_837, c_16, c_23704])).
% 20.77/13.25  tff(c_25261, plain, (![A_310, B_2, A_1]: (k3_xboole_0(k4_xboole_0(A_310, B_2), k3_xboole_0(A_1, B_2))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_24841])).
% 20.77/13.25  tff(c_42599, plain, (![A_403, A_1]: (k3_xboole_0(k3_xboole_0('#skF_1', A_403), k3_xboole_0(A_1, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42558, c_25261])).
% 20.77/13.25  tff(c_253, plain, (![A_44, B_45]: (r1_xboole_0(A_44, B_45) | k3_xboole_0(A_44, B_45)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.77/13.25  tff(c_30, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.77/13.25  tff(c_33, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 20.77/13.25  tff(c_261, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_253, c_33])).
% 20.77/13.25  tff(c_107101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42599, c_261])).
% 20.77/13.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.77/13.25  
% 20.77/13.25  Inference rules
% 20.77/13.25  ----------------------
% 20.77/13.25  #Ref     : 0
% 20.77/13.25  #Sup     : 26308
% 20.77/13.25  #Fact    : 0
% 20.77/13.25  #Define  : 0
% 20.77/13.25  #Split   : 0
% 20.77/13.25  #Chain   : 0
% 20.77/13.25  #Close   : 0
% 20.77/13.25  
% 20.77/13.25  Ordering : KBO
% 20.77/13.25  
% 20.77/13.25  Simplification rules
% 20.77/13.25  ----------------------
% 20.77/13.25  #Subsume      : 72
% 20.77/13.25  #Demod        : 30394
% 20.77/13.25  #Tautology    : 19094
% 20.77/13.25  #SimpNegUnit  : 0
% 20.77/13.25  #BackRed      : 7
% 20.77/13.25  
% 20.77/13.25  #Partial instantiations: 0
% 20.77/13.25  #Strategies tried      : 1
% 20.77/13.25  
% 20.77/13.25  Timing (in seconds)
% 20.77/13.25  ----------------------
% 20.77/13.25  Preprocessing        : 0.32
% 20.77/13.25  Parsing              : 0.17
% 20.77/13.25  CNF conversion       : 0.02
% 20.77/13.25  Main loop            : 12.08
% 20.77/13.25  Inferencing          : 1.44
% 20.77/13.25  Reduction            : 7.84
% 20.77/13.25  Demodulation         : 7.24
% 20.77/13.25  BG Simplification    : 0.17
% 20.77/13.25  Subsumption          : 2.21
% 20.77/13.25  Abstraction          : 0.35
% 20.77/13.25  MUC search           : 0.00
% 20.77/13.25  Cooper               : 0.00
% 20.77/13.25  Total                : 12.45
% 20.77/13.25  Index Insertion      : 0.00
% 20.77/13.25  Index Deletion       : 0.00
% 20.77/13.25  Index Matching       : 0.00
% 20.77/13.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
