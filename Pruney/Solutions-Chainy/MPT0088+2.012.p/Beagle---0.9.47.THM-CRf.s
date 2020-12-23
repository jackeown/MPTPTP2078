%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:21 EST 2020

% Result     : Theorem 11.10s
% Output     : CNFRefutation 11.10s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 130 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   60 ( 125 expanded)
%              Number of equality atoms :   52 ( 114 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_88,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k3_xboole_0(A_22,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_22])).

tff(c_41,plain,(
    ! [B_20,A_21] : k3_xboole_0(B_20,A_21) = k3_xboole_0(A_21,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_21] : k3_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_8])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_129,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_129])).

tff(c_142,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_151,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_142])).

tff(c_166,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_151])).

tff(c_404,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k4_xboole_0(A_40,B_41),C_42) = k4_xboole_0(A_40,k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_455,plain,(
    ! [C_42] : k4_xboole_0('#skF_1',k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_42)) = k4_xboole_0('#skF_1',C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_404])).

tff(c_154,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_142])).

tff(c_167,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_154])).

tff(c_233,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_268,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_233])).

tff(c_279,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_268])).

tff(c_441,plain,(
    ! [A_8,C_42] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_42)) = k4_xboole_0(k1_xboole_0,C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_404])).

tff(c_484,plain,(
    ! [A_8,C_42] : k4_xboole_0(A_8,k2_xboole_0(A_8,C_42)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_441])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_420,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k4_xboole_0(A_40,B_41),k4_xboole_0(A_40,k2_xboole_0(B_41,C_42))) = k3_xboole_0(k4_xboole_0(A_40,B_41),C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_20])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_13497,plain,(
    ! [A_198,B_199,C_200] : k4_xboole_0(k4_xboole_0(A_198,B_199),k4_xboole_0(A_198,k2_xboole_0(B_199,C_200))) = k3_xboole_0(k4_xboole_0(A_198,B_199),C_200) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_20])).

tff(c_13811,plain,(
    ! [A_198,A_6,B_7] : k4_xboole_0(k4_xboole_0(A_198,A_6),k4_xboole_0(A_198,k2_xboole_0(A_6,B_7))) = k3_xboole_0(k4_xboole_0(A_198,A_6),k4_xboole_0(B_7,A_6)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_13497])).

tff(c_30638,plain,(
    ! [A_294,A_295,B_296] : k3_xboole_0(k4_xboole_0(A_294,A_295),k4_xboole_0(B_296,A_295)) = k3_xboole_0(k4_xboole_0(A_294,A_295),B_296) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_13811])).

tff(c_31096,plain,(
    ! [A_294,A_8,C_42] : k3_xboole_0(k4_xboole_0(A_294,k2_xboole_0(A_8,C_42)),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_294,k2_xboole_0(A_8,C_42)),A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_30638])).

tff(c_31316,plain,(
    ! [A_297,A_298,C_299] : k3_xboole_0(k4_xboole_0(A_297,k2_xboole_0(A_298,C_299)),A_298) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_31096])).

tff(c_32780,plain,(
    ! [C_306] : k3_xboole_0(k4_xboole_0('#skF_1',C_306),k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_31316])).

tff(c_13935,plain,(
    ! [A_198,A_6,B_7] : k3_xboole_0(k4_xboole_0(A_198,A_6),k4_xboole_0(B_7,A_6)) = k3_xboole_0(k4_xboole_0(A_198,A_6),B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_13811])).

tff(c_32792,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32780,c_13935])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_265,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,k3_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_233])).

tff(c_877,plain,(
    ! [A_56,B_57] : k3_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_265])).

tff(c_160,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_142])).

tff(c_886,plain,(
    ! [A_56,B_57] : k4_xboole_0(k3_xboole_0(A_56,B_57),k3_xboole_0(A_56,B_57)) = k4_xboole_0(k3_xboole_0(A_56,B_57),A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_160])).

tff(c_946,plain,(
    ! [A_58,B_59] : k4_xboole_0(k3_xboole_0(A_58,B_59),A_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_886])).

tff(c_1105,plain,(
    ! [B_62,A_63] : k4_xboole_0(k3_xboole_0(B_62,A_63),A_63) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_946])).

tff(c_1122,plain,(
    ! [B_62,A_63] : k4_xboole_0(k3_xboole_0(B_62,A_63),k1_xboole_0) = k3_xboole_0(k3_xboole_0(B_62,A_63),A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_1105,c_20])).

tff(c_8270,plain,(
    ! [B_152,A_153] : k3_xboole_0(k3_xboole_0(B_152,A_153),A_153) = k3_xboole_0(B_152,A_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1122])).

tff(c_8393,plain,(
    ! [B_2,A_1] : k3_xboole_0(k3_xboole_0(B_2,A_1),B_2) = k3_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8270])).

tff(c_33171,plain,(
    k3_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_3')) = k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32792,c_8393])).

tff(c_33277,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_33171])).

tff(c_33279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_33277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.10/4.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.10/4.87  
% 11.10/4.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.10/4.87  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.10/4.87  
% 11.10/4.87  %Foreground sorts:
% 11.10/4.87  
% 11.10/4.87  
% 11.10/4.87  %Background operators:
% 11.10/4.87  
% 11.10/4.87  
% 11.10/4.87  %Foreground operators:
% 11.10/4.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.10/4.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.10/4.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.10/4.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.10/4.87  tff('#skF_2', type, '#skF_2': $i).
% 11.10/4.87  tff('#skF_3', type, '#skF_3': $i).
% 11.10/4.87  tff('#skF_1', type, '#skF_1': $i).
% 11.10/4.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.10/4.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.10/4.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.10/4.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.10/4.87  
% 11.10/4.89  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.10/4.89  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 11.10/4.89  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.10/4.89  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.10/4.89  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.10/4.89  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 11.10/4.89  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.10/4.89  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.10/4.89  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.10/4.89  tff(c_88, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k3_xboole_0(A_22, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.10/4.89  tff(c_22, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.10/4.89  tff(c_92, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_22])).
% 11.10/4.89  tff(c_41, plain, (![B_20, A_21]: (k3_xboole_0(B_20, A_21)=k3_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.10/4.89  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.10/4.89  tff(c_57, plain, (![A_21]: (k3_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_41, c_8])).
% 11.10/4.89  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.10/4.89  tff(c_24, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.10/4.89  tff(c_129, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.10/4.89  tff(c_137, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_129])).
% 11.10/4.89  tff(c_142, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.10/4.89  tff(c_151, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_137, c_142])).
% 11.10/4.89  tff(c_166, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_151])).
% 11.10/4.89  tff(c_404, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k4_xboole_0(A_40, B_41), C_42)=k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.10/4.89  tff(c_455, plain, (![C_42]: (k4_xboole_0('#skF_1', k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_42))=k4_xboole_0('#skF_1', C_42))), inference(superposition, [status(thm), theory('equality')], [c_166, c_404])).
% 11.10/4.89  tff(c_154, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_21))), inference(superposition, [status(thm), theory('equality')], [c_57, c_142])).
% 11.10/4.89  tff(c_167, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_154])).
% 11.10/4.89  tff(c_233, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.10/4.89  tff(c_268, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_233])).
% 11.10/4.89  tff(c_279, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_268])).
% 11.10/4.89  tff(c_441, plain, (![A_8, C_42]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_42))=k4_xboole_0(k1_xboole_0, C_42))), inference(superposition, [status(thm), theory('equality')], [c_279, c_404])).
% 11.10/4.89  tff(c_484, plain, (![A_8, C_42]: (k4_xboole_0(A_8, k2_xboole_0(A_8, C_42))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_167, c_441])).
% 11.10/4.89  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.10/4.89  tff(c_420, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k4_xboole_0(A_40, B_41), k4_xboole_0(A_40, k2_xboole_0(B_41, C_42)))=k3_xboole_0(k4_xboole_0(A_40, B_41), C_42))), inference(superposition, [status(thm), theory('equality')], [c_404, c_20])).
% 11.10/4.89  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.10/4.89  tff(c_13497, plain, (![A_198, B_199, C_200]: (k4_xboole_0(k4_xboole_0(A_198, B_199), k4_xboole_0(A_198, k2_xboole_0(B_199, C_200)))=k3_xboole_0(k4_xboole_0(A_198, B_199), C_200))), inference(superposition, [status(thm), theory('equality')], [c_404, c_20])).
% 11.10/4.89  tff(c_13811, plain, (![A_198, A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_198, A_6), k4_xboole_0(A_198, k2_xboole_0(A_6, B_7)))=k3_xboole_0(k4_xboole_0(A_198, A_6), k4_xboole_0(B_7, A_6)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_13497])).
% 11.10/4.89  tff(c_30638, plain, (![A_294, A_295, B_296]: (k3_xboole_0(k4_xboole_0(A_294, A_295), k4_xboole_0(B_296, A_295))=k3_xboole_0(k4_xboole_0(A_294, A_295), B_296))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_13811])).
% 11.10/4.89  tff(c_31096, plain, (![A_294, A_8, C_42]: (k3_xboole_0(k4_xboole_0(A_294, k2_xboole_0(A_8, C_42)), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_294, k2_xboole_0(A_8, C_42)), A_8))), inference(superposition, [status(thm), theory('equality')], [c_484, c_30638])).
% 11.10/4.89  tff(c_31316, plain, (![A_297, A_298, C_299]: (k3_xboole_0(k4_xboole_0(A_297, k2_xboole_0(A_298, C_299)), A_298)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_31096])).
% 11.10/4.89  tff(c_32780, plain, (![C_306]: (k3_xboole_0(k4_xboole_0('#skF_1', C_306), k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_455, c_31316])).
% 11.10/4.89  tff(c_13935, plain, (![A_198, A_6, B_7]: (k3_xboole_0(k4_xboole_0(A_198, A_6), k4_xboole_0(B_7, A_6))=k3_xboole_0(k4_xboole_0(A_198, A_6), B_7))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_13811])).
% 11.10/4.89  tff(c_32792, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_32780, c_13935])).
% 11.10/4.89  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.10/4.89  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.10/4.89  tff(c_265, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, k3_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_233])).
% 11.10/4.89  tff(c_877, plain, (![A_56, B_57]: (k3_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_265])).
% 11.10/4.89  tff(c_160, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_142])).
% 11.10/4.89  tff(c_886, plain, (![A_56, B_57]: (k4_xboole_0(k3_xboole_0(A_56, B_57), k3_xboole_0(A_56, B_57))=k4_xboole_0(k3_xboole_0(A_56, B_57), A_56))), inference(superposition, [status(thm), theory('equality')], [c_877, c_160])).
% 11.10/4.89  tff(c_946, plain, (![A_58, B_59]: (k4_xboole_0(k3_xboole_0(A_58, B_59), A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_279, c_886])).
% 11.10/4.89  tff(c_1105, plain, (![B_62, A_63]: (k4_xboole_0(k3_xboole_0(B_62, A_63), A_63)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_946])).
% 11.10/4.89  tff(c_1122, plain, (![B_62, A_63]: (k4_xboole_0(k3_xboole_0(B_62, A_63), k1_xboole_0)=k3_xboole_0(k3_xboole_0(B_62, A_63), A_63))), inference(superposition, [status(thm), theory('equality')], [c_1105, c_20])).
% 11.10/4.89  tff(c_8270, plain, (![B_152, A_153]: (k3_xboole_0(k3_xboole_0(B_152, A_153), A_153)=k3_xboole_0(B_152, A_153))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1122])).
% 11.10/4.89  tff(c_8393, plain, (![B_2, A_1]: (k3_xboole_0(k3_xboole_0(B_2, A_1), B_2)=k3_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8270])).
% 11.10/4.89  tff(c_33171, plain, (k3_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_3'))=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_32792, c_8393])).
% 11.10/4.89  tff(c_33277, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_57, c_33171])).
% 11.10/4.89  tff(c_33279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_33277])).
% 11.10/4.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.10/4.89  
% 11.10/4.89  Inference rules
% 11.10/4.89  ----------------------
% 11.10/4.89  #Ref     : 0
% 11.10/4.89  #Sup     : 8339
% 11.10/4.89  #Fact    : 0
% 11.10/4.89  #Define  : 0
% 11.10/4.89  #Split   : 0
% 11.10/4.89  #Chain   : 0
% 11.10/4.89  #Close   : 0
% 11.10/4.89  
% 11.10/4.89  Ordering : KBO
% 11.10/4.89  
% 11.10/4.89  Simplification rules
% 11.10/4.89  ----------------------
% 11.10/4.89  #Subsume      : 69
% 11.10/4.89  #Demod        : 9691
% 11.10/4.89  #Tautology    : 5986
% 11.10/4.89  #SimpNegUnit  : 1
% 11.10/4.89  #BackRed      : 12
% 11.10/4.89  
% 11.10/4.89  #Partial instantiations: 0
% 11.10/4.89  #Strategies tried      : 1
% 11.10/4.89  
% 11.10/4.89  Timing (in seconds)
% 11.10/4.89  ----------------------
% 11.10/4.89  Preprocessing        : 0.26
% 11.10/4.89  Parsing              : 0.14
% 11.10/4.89  CNF conversion       : 0.02
% 11.10/4.89  Main loop            : 3.86
% 11.10/4.89  Inferencing          : 0.71
% 11.10/4.89  Reduction            : 2.34
% 11.10/4.89  Demodulation         : 2.13
% 11.10/4.89  BG Simplification    : 0.09
% 11.10/4.89  Subsumption          : 0.56
% 11.10/4.89  Abstraction          : 0.16
% 11.10/4.89  MUC search           : 0.00
% 11.10/4.89  Cooper               : 0.00
% 11.10/4.89  Total                : 4.16
% 11.10/4.89  Index Insertion      : 0.00
% 11.10/4.89  Index Deletion       : 0.00
% 11.10/4.89  Index Matching       : 0.00
% 11.10/4.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
