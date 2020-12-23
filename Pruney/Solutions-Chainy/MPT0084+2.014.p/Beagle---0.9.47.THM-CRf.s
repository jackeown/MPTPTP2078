%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:06 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 183 expanded)
%              Number of leaves         :   22 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :   76 ( 201 expanded)
%              Number of equality atoms :   53 ( 138 expanded)
%              Maximal formula depth    :    8 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(c_281,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(A_37,B_38)
      | k3_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_289,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_281,c_28])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_135,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_151,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_135])).

tff(c_290,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_328,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_290])).

tff(c_339,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_328])).

tff(c_497,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(k3_xboole_0(A_48,B_49),C_50) = k3_xboole_0(A_48,k4_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_533,plain,(
    ! [C_50] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_50)) = k4_xboole_0('#skF_1',C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_497])).

tff(c_46,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_46])).

tff(c_149,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_135])).

tff(c_325,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = k3_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_290])).

tff(c_338,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_325])).

tff(c_405,plain,(
    ! [A_44,B_45] : k2_xboole_0(k3_xboole_0(A_44,B_45),k4_xboole_0(A_44,B_45)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_432,plain,(
    ! [A_10] : k2_xboole_0(k3_xboole_0(A_10,A_10),k1_xboole_0) = A_10 ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_405])).

tff(c_457,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_432])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_150,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_135])).

tff(c_315,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_8,B_9),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_290])).

tff(c_1098,plain,(
    ! [A_64,B_65] : k3_xboole_0(k4_xboole_0(A_64,B_65),A_64) = k4_xboole_0(A_64,B_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_315])).

tff(c_1177,plain,(
    ! [A_1,B_65] : k3_xboole_0(A_1,k4_xboole_0(A_1,B_65)) = k4_xboole_0(A_1,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1098])).

tff(c_18,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_309,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_290])).

tff(c_1723,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_309])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_159,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29,c_159])).

tff(c_429,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_405])).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_447,plain,(
    ! [A_10] : k2_xboole_0(k3_xboole_0(A_10,k1_xboole_0),A_10) = A_10 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_405])).

tff(c_460,plain,(
    ! [A_10] : k2_xboole_0(k1_xboole_0,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_447])).

tff(c_576,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_460])).

tff(c_1246,plain,(
    ! [C_66] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_66)) = k4_xboole_0('#skF_1',C_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_497])).

tff(c_374,plain,(
    ! [A_42,B_43] : r1_tarski(k3_xboole_0(A_42,B_43),A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_14])).

tff(c_392,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_374])).

tff(c_1309,plain,(
    ! [C_67] : r1_tarski(k4_xboole_0('#skF_1',C_67),k4_xboole_0('#skF_3',C_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1246,c_392])).

tff(c_1315,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_1309])).

tff(c_1724,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_1315])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1867,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1724,c_10])).

tff(c_444,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_405])).

tff(c_2330,plain,(
    k2_xboole_0(k3_xboole_0(k4_xboole_0('#skF_3','#skF_2'),'#skF_1'),k1_xboole_0) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1867,c_444])).

tff(c_2352,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_457,c_2,c_2330])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_617,plain,(
    ! [A_53,B_54] : k4_xboole_0(k3_xboole_0(A_53,B_54),A_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_374,c_10])).

tff(c_644,plain,(
    ! [C_15,B_14] : k3_xboole_0(C_15,k4_xboole_0(B_14,C_15)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_617])).

tff(c_1725,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_309])).

tff(c_1806,plain,(
    ! [C_15,B_14] : k4_xboole_0(C_15,k4_xboole_0(B_14,C_15)) = k4_xboole_0(C_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_1725])).

tff(c_1868,plain,(
    ! [C_76,B_77] : k4_xboole_0(C_76,k4_xboole_0(B_77,C_76)) = C_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1806])).

tff(c_1898,plain,(
    ! [B_77,C_76] : k3_xboole_0(k4_xboole_0(B_77,C_76),C_76) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1868,c_644])).

tff(c_2361,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2352,c_1898])).

tff(c_2398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_2361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.62  
% 3.62/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.62  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.62/1.62  
% 3.62/1.62  %Foreground sorts:
% 3.62/1.62  
% 3.62/1.62  
% 3.62/1.62  %Background operators:
% 3.62/1.62  
% 3.62/1.62  
% 3.62/1.62  %Foreground operators:
% 3.62/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.62/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.62/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.62/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.62/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.62/1.62  
% 3.62/1.64  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.62/1.64  tff(f_56, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.62/1.64  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.62/1.64  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.62/1.64  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.62/1.64  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.62/1.64  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.62/1.64  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.62/1.64  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.62/1.64  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.62/1.64  tff(c_281, plain, (![A_37, B_38]: (r1_xboole_0(A_37, B_38) | k3_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.64  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.62/1.64  tff(c_289, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_281, c_28])).
% 3.62/1.64  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.62/1.64  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.62/1.64  tff(c_135, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.62/1.64  tff(c_151, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_135])).
% 3.62/1.64  tff(c_290, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.62/1.64  tff(c_328, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_151, c_290])).
% 3.62/1.64  tff(c_339, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_328])).
% 3.62/1.64  tff(c_497, plain, (![A_48, B_49, C_50]: (k4_xboole_0(k3_xboole_0(A_48, B_49), C_50)=k3_xboole_0(A_48, k4_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.62/1.64  tff(c_533, plain, (![C_50]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_50))=k4_xboole_0('#skF_1', C_50))), inference(superposition, [status(thm), theory('equality')], [c_339, c_497])).
% 3.62/1.64  tff(c_46, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.62/1.64  tff(c_49, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_16, c_46])).
% 3.62/1.64  tff(c_149, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_49, c_135])).
% 3.62/1.64  tff(c_325, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=k3_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_149, c_290])).
% 3.62/1.64  tff(c_338, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_325])).
% 3.62/1.64  tff(c_405, plain, (![A_44, B_45]: (k2_xboole_0(k3_xboole_0(A_44, B_45), k4_xboole_0(A_44, B_45))=A_44)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.62/1.64  tff(c_432, plain, (![A_10]: (k2_xboole_0(k3_xboole_0(A_10, A_10), k1_xboole_0)=A_10)), inference(superposition, [status(thm), theory('equality')], [c_149, c_405])).
% 3.62/1.64  tff(c_457, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_338, c_432])).
% 3.62/1.64  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.62/1.64  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.62/1.64  tff(c_150, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_135])).
% 3.62/1.64  tff(c_315, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_8, B_9), A_8))), inference(superposition, [status(thm), theory('equality')], [c_150, c_290])).
% 3.62/1.64  tff(c_1098, plain, (![A_64, B_65]: (k3_xboole_0(k4_xboole_0(A_64, B_65), A_64)=k4_xboole_0(A_64, B_65))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_315])).
% 3.62/1.64  tff(c_1177, plain, (![A_1, B_65]: (k3_xboole_0(A_1, k4_xboole_0(A_1, B_65))=k4_xboole_0(A_1, B_65))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1098])).
% 3.62/1.64  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.62/1.64  tff(c_309, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k3_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_290])).
% 3.62/1.64  tff(c_1723, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_1177, c_309])).
% 3.62/1.64  tff(c_24, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.62/1.64  tff(c_29, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 3.62/1.64  tff(c_159, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.64  tff(c_163, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_29, c_159])).
% 3.62/1.64  tff(c_429, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2')))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_163, c_405])).
% 3.62/1.64  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.62/1.64  tff(c_447, plain, (![A_10]: (k2_xboole_0(k3_xboole_0(A_10, k1_xboole_0), A_10)=A_10)), inference(superposition, [status(thm), theory('equality')], [c_16, c_405])).
% 3.62/1.64  tff(c_460, plain, (![A_10]: (k2_xboole_0(k1_xboole_0, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_447])).
% 3.62/1.64  tff(c_576, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_429, c_460])).
% 3.62/1.64  tff(c_1246, plain, (![C_66]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_66))=k4_xboole_0('#skF_1', C_66))), inference(superposition, [status(thm), theory('equality')], [c_339, c_497])).
% 3.62/1.64  tff(c_374, plain, (![A_42, B_43]: (r1_tarski(k3_xboole_0(A_42, B_43), A_42))), inference(superposition, [status(thm), theory('equality')], [c_290, c_14])).
% 3.62/1.64  tff(c_392, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_374])).
% 3.62/1.64  tff(c_1309, plain, (![C_67]: (r1_tarski(k4_xboole_0('#skF_1', C_67), k4_xboole_0('#skF_3', C_67)))), inference(superposition, [status(thm), theory('equality')], [c_1246, c_392])).
% 3.62/1.64  tff(c_1315, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_576, c_1309])).
% 3.62/1.64  tff(c_1724, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_1315])).
% 3.62/1.64  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.62/1.64  tff(c_1867, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1724, c_10])).
% 3.62/1.64  tff(c_444, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_405])).
% 3.62/1.64  tff(c_2330, plain, (k2_xboole_0(k3_xboole_0(k4_xboole_0('#skF_3', '#skF_2'), '#skF_1'), k1_xboole_0)='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1867, c_444])).
% 3.62/1.64  tff(c_2352, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_533, c_457, c_2, c_2330])).
% 3.62/1.64  tff(c_20, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k3_xboole_0(A_13, B_14), C_15)=k3_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.62/1.64  tff(c_617, plain, (![A_53, B_54]: (k4_xboole_0(k3_xboole_0(A_53, B_54), A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_374, c_10])).
% 3.62/1.64  tff(c_644, plain, (![C_15, B_14]: (k3_xboole_0(C_15, k4_xboole_0(B_14, C_15))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_617])).
% 3.62/1.64  tff(c_1725, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(demodulation, [status(thm), theory('equality')], [c_1177, c_309])).
% 3.62/1.64  tff(c_1806, plain, (![C_15, B_14]: (k4_xboole_0(C_15, k4_xboole_0(B_14, C_15))=k4_xboole_0(C_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_644, c_1725])).
% 3.62/1.64  tff(c_1868, plain, (![C_76, B_77]: (k4_xboole_0(C_76, k4_xboole_0(B_77, C_76))=C_76)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1806])).
% 3.62/1.64  tff(c_1898, plain, (![B_77, C_76]: (k3_xboole_0(k4_xboole_0(B_77, C_76), C_76)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1868, c_644])).
% 3.62/1.64  tff(c_2361, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2352, c_1898])).
% 3.62/1.64  tff(c_2398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_289, c_2361])).
% 3.62/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.64  
% 3.62/1.64  Inference rules
% 3.62/1.64  ----------------------
% 3.62/1.64  #Ref     : 0
% 3.62/1.64  #Sup     : 604
% 3.62/1.64  #Fact    : 0
% 3.62/1.64  #Define  : 0
% 3.62/1.64  #Split   : 0
% 3.62/1.64  #Chain   : 0
% 3.62/1.64  #Close   : 0
% 3.62/1.64  
% 3.62/1.64  Ordering : KBO
% 3.62/1.64  
% 3.62/1.64  Simplification rules
% 3.62/1.64  ----------------------
% 3.62/1.64  #Subsume      : 0
% 3.62/1.64  #Demod        : 511
% 3.62/1.64  #Tautology    : 415
% 3.62/1.64  #SimpNegUnit  : 1
% 3.62/1.64  #BackRed      : 2
% 3.62/1.64  
% 3.62/1.64  #Partial instantiations: 0
% 3.62/1.64  #Strategies tried      : 1
% 3.62/1.64  
% 3.62/1.64  Timing (in seconds)
% 3.62/1.64  ----------------------
% 3.62/1.64  Preprocessing        : 0.31
% 3.62/1.64  Parsing              : 0.17
% 3.62/1.64  CNF conversion       : 0.02
% 3.62/1.64  Main loop            : 0.54
% 3.62/1.64  Inferencing          : 0.18
% 3.62/1.64  Reduction            : 0.24
% 3.62/1.64  Demodulation         : 0.20
% 3.62/1.64  BG Simplification    : 0.02
% 3.62/1.64  Subsumption          : 0.07
% 3.62/1.64  Abstraction          : 0.03
% 3.62/1.64  MUC search           : 0.00
% 3.62/1.64  Cooper               : 0.00
% 3.62/1.64  Total                : 0.88
% 3.62/1.64  Index Insertion      : 0.00
% 3.62/1.64  Index Deletion       : 0.00
% 3.62/1.64  Index Matching       : 0.00
% 3.62/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
