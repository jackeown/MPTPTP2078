%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:20 EST 2020

% Result     : Theorem 12.44s
% Output     : CNFRefutation 12.44s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   56 (  91 expanded)
%              Number of equality atoms :   42 (  67 expanded)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_74,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_24])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_80,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_80])).

tff(c_244,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_288,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_244])).

tff(c_298,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_288])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_458,plain,(
    ! [A_49,B_50,C_51] : k4_xboole_0(k3_xboole_0(A_49,B_50),C_51) = k3_xboole_0(A_49,k4_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13486,plain,(
    ! [A_203,B_204,C_205] : k4_xboole_0(k3_xboole_0(A_203,B_204),k3_xboole_0(A_203,k4_xboole_0(B_204,C_205))) = k3_xboole_0(k3_xboole_0(A_203,B_204),C_205) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_20])).

tff(c_13919,plain,(
    ! [A_203,A_7,B_8] : k4_xboole_0(k3_xboole_0(A_203,k4_xboole_0(A_7,B_8)),k3_xboole_0(A_203,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(A_203,k4_xboole_0(A_7,B_8)),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_13486])).

tff(c_42414,plain,(
    ! [A_345,A_346,B_347] : k3_xboole_0(k3_xboole_0(A_345,k4_xboole_0(A_346,B_347)),A_346) = k3_xboole_0(A_345,k4_xboole_0(A_346,B_347)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_298,c_13919])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_299,plain,(
    ! [A_43,B_44,C_45] : k4_xboole_0(k4_xboole_0(A_43,B_44),C_45) = k4_xboole_0(A_43,k2_xboole_0(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_343,plain,(
    ! [A_15,B_16,C_45] : k4_xboole_0(A_15,k2_xboole_0(k4_xboole_0(A_15,B_16),C_45)) = k4_xboole_0(k3_xboole_0(A_15,B_16),C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_299])).

tff(c_3839,plain,(
    ! [A_15,B_16,C_45] : k4_xboole_0(A_15,k2_xboole_0(k4_xboole_0(A_15,B_16),C_45)) = k3_xboole_0(A_15,k4_xboole_0(B_16,C_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_343])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_188,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_196,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_188])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_227,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_18])).

tff(c_230,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_227])).

tff(c_312,plain,(
    ! [A_43,B_44,B_16] : k4_xboole_0(A_43,k2_xboole_0(B_44,k4_xboole_0(k4_xboole_0(A_43,B_44),B_16))) = k3_xboole_0(k4_xboole_0(A_43,B_44),B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_20])).

tff(c_6410,plain,(
    ! [A_140,B_141,B_142] : k4_xboole_0(A_140,k2_xboole_0(B_141,k4_xboole_0(A_140,k2_xboole_0(B_141,B_142)))) = k3_xboole_0(k4_xboole_0(A_140,B_141),B_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_312])).

tff(c_7088,plain,(
    ! [A_149,B_150,B_151] : k4_xboole_0(k3_xboole_0(k4_xboole_0(A_149,B_150),B_151),A_149) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6410,c_92])).

tff(c_7846,plain,(
    ! [C_156,B_157,B_158] : k3_xboole_0(k4_xboole_0(C_156,B_157),k4_xboole_0(B_158,C_156)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_7088])).

tff(c_8112,plain,(
    ! [B_157] : k3_xboole_0(k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),B_157),'#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_7846])).

tff(c_9327,plain,(
    ! [B_168] : k3_xboole_0(k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',B_168)),'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8112])).

tff(c_17953,plain,(
    ! [A_228] : k3_xboole_0(k4_xboole_0('#skF_2',k2_xboole_0(A_228,'#skF_3')),'#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9327])).

tff(c_18057,plain,(
    ! [B_16] : k3_xboole_0(k3_xboole_0('#skF_2',k4_xboole_0(B_16,'#skF_3')),'#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3839,c_17953])).

tff(c_42432,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42414,c_18057])).

tff(c_43025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_42432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:51:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.44/5.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.44/5.85  
% 12.44/5.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.44/5.86  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.44/5.86  
% 12.44/5.86  %Foreground sorts:
% 12.44/5.86  
% 12.44/5.86  
% 12.44/5.86  %Background operators:
% 12.44/5.86  
% 12.44/5.86  
% 12.44/5.86  %Foreground operators:
% 12.44/5.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.44/5.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.44/5.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.44/5.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.44/5.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.44/5.86  tff('#skF_2', type, '#skF_2': $i).
% 12.44/5.86  tff('#skF_3', type, '#skF_3': $i).
% 12.44/5.86  tff('#skF_1', type, '#skF_1': $i).
% 12.44/5.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.44/5.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.44/5.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.44/5.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.44/5.86  
% 12.44/5.87  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.44/5.87  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 12.44/5.87  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 12.44/5.87  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.44/5.87  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.44/5.87  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.44/5.87  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 12.44/5.87  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.44/5.87  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.44/5.87  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 12.44/5.87  tff(c_74, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.44/5.87  tff(c_24, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.44/5.87  tff(c_78, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_24])).
% 12.44/5.87  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.44/5.87  tff(c_36, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.44/5.87  tff(c_39, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_14, c_36])).
% 12.44/5.87  tff(c_80, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.44/5.87  tff(c_91, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_39, c_80])).
% 12.44/5.87  tff(c_244, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.44/5.87  tff(c_288, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_244])).
% 12.44/5.87  tff(c_298, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_288])).
% 12.44/5.87  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.44/5.87  tff(c_92, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_80])).
% 12.44/5.87  tff(c_458, plain, (![A_49, B_50, C_51]: (k4_xboole_0(k3_xboole_0(A_49, B_50), C_51)=k3_xboole_0(A_49, k4_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.44/5.87  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.44/5.87  tff(c_13486, plain, (![A_203, B_204, C_205]: (k4_xboole_0(k3_xboole_0(A_203, B_204), k3_xboole_0(A_203, k4_xboole_0(B_204, C_205)))=k3_xboole_0(k3_xboole_0(A_203, B_204), C_205))), inference(superposition, [status(thm), theory('equality')], [c_458, c_20])).
% 12.44/5.87  tff(c_13919, plain, (![A_203, A_7, B_8]: (k4_xboole_0(k3_xboole_0(A_203, k4_xboole_0(A_7, B_8)), k3_xboole_0(A_203, k1_xboole_0))=k3_xboole_0(k3_xboole_0(A_203, k4_xboole_0(A_7, B_8)), A_7))), inference(superposition, [status(thm), theory('equality')], [c_92, c_13486])).
% 12.44/5.87  tff(c_42414, plain, (![A_345, A_346, B_347]: (k3_xboole_0(k3_xboole_0(A_345, k4_xboole_0(A_346, B_347)), A_346)=k3_xboole_0(A_345, k4_xboole_0(A_346, B_347)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_298, c_13919])).
% 12.44/5.87  tff(c_22, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), C_19)=k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.44/5.87  tff(c_299, plain, (![A_43, B_44, C_45]: (k4_xboole_0(k4_xboole_0(A_43, B_44), C_45)=k4_xboole_0(A_43, k2_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.44/5.87  tff(c_343, plain, (![A_15, B_16, C_45]: (k4_xboole_0(A_15, k2_xboole_0(k4_xboole_0(A_15, B_16), C_45))=k4_xboole_0(k3_xboole_0(A_15, B_16), C_45))), inference(superposition, [status(thm), theory('equality')], [c_20, c_299])).
% 12.44/5.87  tff(c_3839, plain, (![A_15, B_16, C_45]: (k4_xboole_0(A_15, k2_xboole_0(k4_xboole_0(A_15, B_16), C_45))=k3_xboole_0(A_15, k4_xboole_0(B_16, C_45)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_343])).
% 12.44/5.87  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.44/5.87  tff(c_16, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.44/5.87  tff(c_26, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.44/5.87  tff(c_188, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.44/5.87  tff(c_196, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_188])).
% 12.44/5.87  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.44/5.87  tff(c_227, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_196, c_18])).
% 12.44/5.87  tff(c_230, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_227])).
% 12.44/5.87  tff(c_312, plain, (![A_43, B_44, B_16]: (k4_xboole_0(A_43, k2_xboole_0(B_44, k4_xboole_0(k4_xboole_0(A_43, B_44), B_16)))=k3_xboole_0(k4_xboole_0(A_43, B_44), B_16))), inference(superposition, [status(thm), theory('equality')], [c_299, c_20])).
% 12.44/5.87  tff(c_6410, plain, (![A_140, B_141, B_142]: (k4_xboole_0(A_140, k2_xboole_0(B_141, k4_xboole_0(A_140, k2_xboole_0(B_141, B_142))))=k3_xboole_0(k4_xboole_0(A_140, B_141), B_142))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_312])).
% 12.44/5.87  tff(c_7088, plain, (![A_149, B_150, B_151]: (k4_xboole_0(k3_xboole_0(k4_xboole_0(A_149, B_150), B_151), A_149)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6410, c_92])).
% 12.44/5.87  tff(c_7846, plain, (![C_156, B_157, B_158]: (k3_xboole_0(k4_xboole_0(C_156, B_157), k4_xboole_0(B_158, C_156))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_7088])).
% 12.44/5.87  tff(c_8112, plain, (![B_157]: (k3_xboole_0(k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), B_157), '#skF_1')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_230, c_7846])).
% 12.44/5.87  tff(c_9327, plain, (![B_168]: (k3_xboole_0(k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', B_168)), '#skF_1')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8112])).
% 12.44/5.87  tff(c_17953, plain, (![A_228]: (k3_xboole_0(k4_xboole_0('#skF_2', k2_xboole_0(A_228, '#skF_3')), '#skF_1')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_9327])).
% 12.44/5.87  tff(c_18057, plain, (![B_16]: (k3_xboole_0(k3_xboole_0('#skF_2', k4_xboole_0(B_16, '#skF_3')), '#skF_1')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3839, c_17953])).
% 12.44/5.87  tff(c_42432, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42414, c_18057])).
% 12.44/5.87  tff(c_43025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_42432])).
% 12.44/5.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.44/5.87  
% 12.44/5.87  Inference rules
% 12.44/5.87  ----------------------
% 12.44/5.87  #Ref     : 0
% 12.44/5.87  #Sup     : 10710
% 12.44/5.87  #Fact    : 0
% 12.44/5.87  #Define  : 0
% 12.44/5.87  #Split   : 0
% 12.44/5.87  #Chain   : 0
% 12.44/5.87  #Close   : 0
% 12.44/5.87  
% 12.44/5.87  Ordering : KBO
% 12.44/5.87  
% 12.44/5.87  Simplification rules
% 12.44/5.87  ----------------------
% 12.44/5.87  #Subsume      : 6
% 12.44/5.87  #Demod        : 12753
% 12.44/5.87  #Tautology    : 7671
% 12.44/5.87  #SimpNegUnit  : 1
% 12.44/5.87  #BackRed      : 0
% 12.44/5.87  
% 12.44/5.87  #Partial instantiations: 0
% 12.44/5.87  #Strategies tried      : 1
% 12.44/5.87  
% 12.44/5.87  Timing (in seconds)
% 12.44/5.87  ----------------------
% 12.44/5.87  Preprocessing        : 0.30
% 12.44/5.87  Parsing              : 0.16
% 12.44/5.87  CNF conversion       : 0.02
% 12.44/5.87  Main loop            : 4.76
% 12.44/5.87  Inferencing          : 0.78
% 12.44/5.87  Reduction            : 2.88
% 12.44/5.87  Demodulation         : 2.61
% 12.44/5.87  BG Simplification    : 0.09
% 12.44/5.87  Subsumption          : 0.81
% 12.44/5.87  Abstraction          : 0.16
% 12.44/5.87  MUC search           : 0.00
% 12.44/5.87  Cooper               : 0.00
% 12.44/5.87  Total                : 5.10
% 12.44/5.87  Index Insertion      : 0.00
% 12.44/5.88  Index Deletion       : 0.00
% 12.44/5.88  Index Matching       : 0.00
% 12.44/5.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
