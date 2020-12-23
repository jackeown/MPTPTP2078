%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:21 EST 2020

% Result     : Theorem 10.82s
% Output     : CNFRefutation 10.94s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 133 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :   61 ( 128 expanded)
%              Number of equality atoms :   53 ( 117 expanded)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_140,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_144,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_140,c_22])).

tff(c_58,plain,(
    ! [B_20,A_21] : k3_xboole_0(B_20,A_21) = k3_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [A_21] : k3_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_8])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_146])).

tff(c_290,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k3_xboole_0(A_34,B_35)) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_312,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_290])).

tff(c_334,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_312])).

tff(c_518,plain,(
    ! [A_42,B_43,C_44] : k4_xboole_0(k4_xboole_0(A_42,B_43),C_44) = k4_xboole_0(A_42,k2_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_569,plain,(
    ! [C_44] : k4_xboole_0('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_44)) = k4_xboole_0('#skF_1',C_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_518])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_176,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_198,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_176])).

tff(c_209,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_198])).

tff(c_579,plain,(
    ! [A_8,C_44] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_44)) = k4_xboole_0(k1_xboole_0,C_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_518])).

tff(c_614,plain,(
    ! [A_8,C_44] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_44)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_579])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_543,plain,(
    ! [A_42,B_43,B_15] : k4_xboole_0(A_42,k2_xboole_0(B_43,k4_xboole_0(k4_xboole_0(A_42,B_43),B_15))) = k3_xboole_0(k4_xboole_0(A_42,B_43),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_18])).

tff(c_606,plain,(
    ! [A_42,B_43,B_15] : k4_xboole_0(A_42,k2_xboole_0(B_43,k4_xboole_0(A_42,k2_xboole_0(B_43,B_15)))) = k3_xboole_0(k4_xboole_0(A_42,B_43),B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_543])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6839,plain,(
    ! [A_139,B_140,B_141] : k4_xboole_0(A_139,k2_xboole_0(B_140,k4_xboole_0(A_139,k2_xboole_0(B_140,B_141)))) = k3_xboole_0(k4_xboole_0(A_139,B_140),B_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_543])).

tff(c_7102,plain,(
    ! [A_139,A_6,B_7] : k4_xboole_0(A_139,k2_xboole_0(A_6,k4_xboole_0(A_139,k2_xboole_0(A_6,B_7)))) = k3_xboole_0(k4_xboole_0(A_139,A_6),k4_xboole_0(B_7,A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_6839])).

tff(c_32042,plain,(
    ! [A_297,A_298,B_299] : k3_xboole_0(k4_xboole_0(A_297,A_298),k4_xboole_0(B_299,A_298)) = k3_xboole_0(k4_xboole_0(A_297,A_298),B_299) ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_7102])).

tff(c_32523,plain,(
    ! [A_297,A_8,C_44] : k3_xboole_0(k4_xboole_0(A_297,k2_xboole_0(A_8,C_44)),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_297,k2_xboole_0(A_8,C_44)),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_32042])).

tff(c_32760,plain,(
    ! [A_300,A_301,C_302] : k3_xboole_0(k4_xboole_0(A_300,k2_xboole_0(A_301,C_302)),A_301) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32523])).

tff(c_34655,plain,(
    ! [C_310] : k3_xboole_0(k4_xboole_0('#skF_1',C_310),k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_32760])).

tff(c_7172,plain,(
    ! [A_139,A_6,B_7] : k3_xboole_0(k4_xboole_0(A_139,A_6),k4_xboole_0(B_7,A_6)) = k3_xboole_0(k4_xboole_0(A_139,A_6),B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_7102])).

tff(c_34667,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34655,c_7172])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_296,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,k3_xboole_0(A_34,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_18])).

tff(c_411,plain,(
    ! [A_38,B_39] : k3_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_296])).

tff(c_318,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_290])).

tff(c_420,plain,(
    ! [A_38,B_39] : k4_xboole_0(k3_xboole_0(A_38,B_39),k3_xboole_0(A_38,B_39)) = k4_xboole_0(k3_xboole_0(A_38,B_39),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_318])).

tff(c_468,plain,(
    ! [A_40,B_41] : k4_xboole_0(k3_xboole_0(A_40,B_41),A_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_420])).

tff(c_739,plain,(
    ! [B_49,A_50] : k4_xboole_0(k3_xboole_0(B_49,A_50),A_50) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_468])).

tff(c_750,plain,(
    ! [B_49,A_50] : k4_xboole_0(k3_xboole_0(B_49,A_50),k1_xboole_0) = k3_xboole_0(k3_xboole_0(B_49,A_50),A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_18])).

tff(c_13132,plain,(
    ! [B_188,A_189] : k3_xboole_0(k3_xboole_0(B_188,A_189),A_189) = k3_xboole_0(B_188,A_189) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_750])).

tff(c_13315,plain,(
    ! [B_2,A_1] : k3_xboole_0(k3_xboole_0(B_2,A_1),B_2) = k3_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13132])).

tff(c_35003,plain,(
    k3_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_3')) = k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34667,c_13315])).

tff(c_35139,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_35003])).

tff(c_35141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_35139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:21:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.82/4.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/4.94  
% 10.82/4.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/4.94  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.82/4.94  
% 10.82/4.94  %Foreground sorts:
% 10.82/4.94  
% 10.82/4.94  
% 10.82/4.94  %Background operators:
% 10.82/4.94  
% 10.82/4.94  
% 10.82/4.94  %Foreground operators:
% 10.82/4.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.82/4.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.82/4.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.82/4.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.82/4.94  tff('#skF_2', type, '#skF_2': $i).
% 10.82/4.94  tff('#skF_3', type, '#skF_3': $i).
% 10.82/4.94  tff('#skF_1', type, '#skF_1': $i).
% 10.82/4.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.82/4.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.82/4.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.82/4.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.82/4.94  
% 10.94/4.96  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.94/4.96  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 10.94/4.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.94/4.96  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.94/4.96  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.94/4.96  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 10.94/4.96  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.94/4.96  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 10.94/4.96  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.94/4.96  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.94/4.96  tff(c_140, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.94/4.96  tff(c_22, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.94/4.96  tff(c_144, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_140, c_22])).
% 10.94/4.96  tff(c_58, plain, (![B_20, A_21]: (k3_xboole_0(B_20, A_21)=k3_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.94/4.96  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.94/4.96  tff(c_74, plain, (![A_21]: (k3_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_8])).
% 10.94/4.96  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.94/4.96  tff(c_24, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.94/4.96  tff(c_146, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.94/4.96  tff(c_154, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_146])).
% 10.94/4.96  tff(c_290, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k3_xboole_0(A_34, B_35))=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.94/4.96  tff(c_312, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_154, c_290])).
% 10.94/4.96  tff(c_334, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_312])).
% 10.94/4.96  tff(c_518, plain, (![A_42, B_43, C_44]: (k4_xboole_0(k4_xboole_0(A_42, B_43), C_44)=k4_xboole_0(A_42, k2_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.94/4.96  tff(c_569, plain, (![C_44]: (k4_xboole_0('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_44))=k4_xboole_0('#skF_1', C_44))), inference(superposition, [status(thm), theory('equality')], [c_334, c_518])).
% 10.94/4.96  tff(c_20, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.94/4.96  tff(c_176, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.94/4.96  tff(c_198, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_176])).
% 10.94/4.96  tff(c_209, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_198])).
% 10.94/4.96  tff(c_579, plain, (![A_8, C_44]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_44))=k4_xboole_0(k1_xboole_0, C_44))), inference(superposition, [status(thm), theory('equality')], [c_209, c_518])).
% 10.94/4.96  tff(c_614, plain, (![A_8, C_44]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_44))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_579])).
% 10.94/4.96  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.94/4.96  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.94/4.96  tff(c_543, plain, (![A_42, B_43, B_15]: (k4_xboole_0(A_42, k2_xboole_0(B_43, k4_xboole_0(k4_xboole_0(A_42, B_43), B_15)))=k3_xboole_0(k4_xboole_0(A_42, B_43), B_15))), inference(superposition, [status(thm), theory('equality')], [c_518, c_18])).
% 10.94/4.96  tff(c_606, plain, (![A_42, B_43, B_15]: (k4_xboole_0(A_42, k2_xboole_0(B_43, k4_xboole_0(A_42, k2_xboole_0(B_43, B_15))))=k3_xboole_0(k4_xboole_0(A_42, B_43), B_15))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_543])).
% 10.94/4.96  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.94/4.96  tff(c_6839, plain, (![A_139, B_140, B_141]: (k4_xboole_0(A_139, k2_xboole_0(B_140, k4_xboole_0(A_139, k2_xboole_0(B_140, B_141))))=k3_xboole_0(k4_xboole_0(A_139, B_140), B_141))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_543])).
% 10.94/4.96  tff(c_7102, plain, (![A_139, A_6, B_7]: (k4_xboole_0(A_139, k2_xboole_0(A_6, k4_xboole_0(A_139, k2_xboole_0(A_6, B_7))))=k3_xboole_0(k4_xboole_0(A_139, A_6), k4_xboole_0(B_7, A_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_6839])).
% 10.94/4.96  tff(c_32042, plain, (![A_297, A_298, B_299]: (k3_xboole_0(k4_xboole_0(A_297, A_298), k4_xboole_0(B_299, A_298))=k3_xboole_0(k4_xboole_0(A_297, A_298), B_299))), inference(demodulation, [status(thm), theory('equality')], [c_606, c_7102])).
% 10.94/4.96  tff(c_32523, plain, (![A_297, A_8, C_44]: (k3_xboole_0(k4_xboole_0(A_297, k2_xboole_0(A_8, C_44)), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_297, k2_xboole_0(A_8, C_44)), A_8))), inference(superposition, [status(thm), theory('equality')], [c_614, c_32042])).
% 10.94/4.96  tff(c_32760, plain, (![A_300, A_301, C_302]: (k3_xboole_0(k4_xboole_0(A_300, k2_xboole_0(A_301, C_302)), A_301)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32523])).
% 10.94/4.96  tff(c_34655, plain, (![C_310]: (k3_xboole_0(k4_xboole_0('#skF_1', C_310), k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_569, c_32760])).
% 10.94/4.96  tff(c_7172, plain, (![A_139, A_6, B_7]: (k3_xboole_0(k4_xboole_0(A_139, A_6), k4_xboole_0(B_7, A_6))=k3_xboole_0(k4_xboole_0(A_139, A_6), B_7))), inference(demodulation, [status(thm), theory('equality')], [c_606, c_7102])).
% 10.94/4.96  tff(c_34667, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34655, c_7172])).
% 10.94/4.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.94/4.96  tff(c_296, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, k3_xboole_0(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_290, c_18])).
% 10.94/4.96  tff(c_411, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_296])).
% 10.94/4.96  tff(c_318, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_290])).
% 10.94/4.96  tff(c_420, plain, (![A_38, B_39]: (k4_xboole_0(k3_xboole_0(A_38, B_39), k3_xboole_0(A_38, B_39))=k4_xboole_0(k3_xboole_0(A_38, B_39), A_38))), inference(superposition, [status(thm), theory('equality')], [c_411, c_318])).
% 10.94/4.96  tff(c_468, plain, (![A_40, B_41]: (k4_xboole_0(k3_xboole_0(A_40, B_41), A_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_209, c_420])).
% 10.94/4.96  tff(c_739, plain, (![B_49, A_50]: (k4_xboole_0(k3_xboole_0(B_49, A_50), A_50)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_468])).
% 10.94/4.96  tff(c_750, plain, (![B_49, A_50]: (k4_xboole_0(k3_xboole_0(B_49, A_50), k1_xboole_0)=k3_xboole_0(k3_xboole_0(B_49, A_50), A_50))), inference(superposition, [status(thm), theory('equality')], [c_739, c_18])).
% 10.94/4.96  tff(c_13132, plain, (![B_188, A_189]: (k3_xboole_0(k3_xboole_0(B_188, A_189), A_189)=k3_xboole_0(B_188, A_189))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_750])).
% 10.94/4.96  tff(c_13315, plain, (![B_2, A_1]: (k3_xboole_0(k3_xboole_0(B_2, A_1), B_2)=k3_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_13132])).
% 10.94/4.96  tff(c_35003, plain, (k3_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_3'))=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_34667, c_13315])).
% 10.94/4.96  tff(c_35139, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_35003])).
% 10.94/4.96  tff(c_35141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_35139])).
% 10.94/4.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.94/4.96  
% 10.94/4.96  Inference rules
% 10.94/4.96  ----------------------
% 10.94/4.96  #Ref     : 0
% 10.94/4.96  #Sup     : 8711
% 10.94/4.96  #Fact    : 0
% 10.94/4.96  #Define  : 0
% 10.94/4.96  #Split   : 0
% 10.94/4.96  #Chain   : 0
% 10.94/4.96  #Close   : 0
% 10.94/4.96  
% 10.94/4.96  Ordering : KBO
% 10.94/4.96  
% 10.94/4.96  Simplification rules
% 10.94/4.96  ----------------------
% 10.94/4.96  #Subsume      : 50
% 10.94/4.96  #Demod        : 10634
% 10.94/4.96  #Tautology    : 6063
% 10.94/4.96  #SimpNegUnit  : 1
% 10.94/4.96  #BackRed      : 15
% 10.94/4.96  
% 10.94/4.96  #Partial instantiations: 0
% 10.94/4.96  #Strategies tried      : 1
% 10.94/4.96  
% 10.94/4.96  Timing (in seconds)
% 10.94/4.96  ----------------------
% 10.94/4.96  Preprocessing        : 0.26
% 10.94/4.96  Parsing              : 0.14
% 10.94/4.96  CNF conversion       : 0.02
% 10.94/4.96  Main loop            : 3.92
% 10.94/4.96  Inferencing          : 0.70
% 10.94/4.96  Reduction            : 2.41
% 10.94/4.96  Demodulation         : 2.19
% 10.94/4.96  BG Simplification    : 0.08
% 10.94/4.96  Subsumption          : 0.57
% 10.94/4.96  Abstraction          : 0.16
% 10.94/4.96  MUC search           : 0.00
% 10.94/4.96  Cooper               : 0.00
% 10.94/4.96  Total                : 4.21
% 10.94/4.96  Index Insertion      : 0.00
% 10.94/4.96  Index Deletion       : 0.00
% 10.94/4.96  Index Matching       : 0.00
% 10.94/4.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
