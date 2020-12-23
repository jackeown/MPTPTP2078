%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:20 EST 2020

% Result     : Theorem 13.09s
% Output     : CNFRefutation 13.09s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 107 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 ( 102 expanded)
%              Number of equality atoms :   47 (  91 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_83,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_91,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_22])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_107,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_92])).

tff(c_110,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_107])).

tff(c_151,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = k2_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_151])).

tff(c_570,plain,(
    ! [A_48,B_49,C_50] : k4_xboole_0(k4_xboole_0(A_48,B_49),C_50) = k4_xboole_0(A_48,k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1349,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k2_xboole_0(B_65,k1_xboole_0)) = k4_xboole_0(A_64,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_570])).

tff(c_1434,plain,(
    ! [A_64,A_8] : k4_xboole_0(A_64,k2_xboole_0(A_8,A_8)) = k4_xboole_0(A_64,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_1349])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_74,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_74])).

tff(c_276,plain,(
    ! [A_37,B_38,C_39] : k4_xboole_0(k3_xboole_0(A_37,B_38),C_39) = k3_xboole_0(A_37,k4_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7430,plain,(
    ! [C_133,A_134,B_135] : k2_xboole_0(C_133,k3_xboole_0(A_134,k4_xboole_0(B_135,C_133))) = k2_xboole_0(C_133,k3_xboole_0(A_134,B_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_10])).

tff(c_7676,plain,(
    k2_xboole_0('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_7430])).

tff(c_7735,plain,(
    k2_xboole_0('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k2_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_7676])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_617,plain,(
    ! [A_12,B_13,C_50] : k4_xboole_0(A_12,k2_xboole_0(k3_xboole_0(A_12,B_13),C_50)) = k4_xboole_0(k4_xboole_0(A_12,B_13),C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_570])).

tff(c_4211,plain,(
    ! [A_105,B_106,C_107] : k4_xboole_0(A_105,k2_xboole_0(k3_xboole_0(A_105,B_106),C_107)) = k4_xboole_0(A_105,k2_xboole_0(B_106,C_107)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_617])).

tff(c_49859,plain,(
    ! [A_352,A_353,B_354] : k4_xboole_0(A_352,k2_xboole_0(A_353,k3_xboole_0(A_352,B_354))) = k4_xboole_0(A_352,k2_xboole_0(B_354,A_353)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4211])).

tff(c_50353,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7735,c_49859])).

tff(c_50606,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1434,c_2,c_50353])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k3_xboole_0(A_16,B_17),C_18) = k3_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_631,plain,(
    ! [A_14,B_15,C_50] : k4_xboole_0(A_14,k2_xboole_0(k4_xboole_0(A_14,B_15),C_50)) = k4_xboole_0(k3_xboole_0(A_14,B_15),C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_570])).

tff(c_654,plain,(
    ! [A_14,B_15,C_50] : k4_xboole_0(A_14,k2_xboole_0(k4_xboole_0(A_14,B_15),C_50)) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_631])).

tff(c_605,plain,(
    ! [A_9,B_10,C_11,C_50] : k4_xboole_0(k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)),C_50) = k4_xboole_0(k4_xboole_0(A_9,B_10),k2_xboole_0(C_11,C_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_570])).

tff(c_9697,plain,(
    ! [A_152,B_153,C_154,C_155] : k4_xboole_0(A_152,k2_xboole_0(k2_xboole_0(B_153,C_154),C_155)) = k4_xboole_0(A_152,k2_xboole_0(B_153,k2_xboole_0(C_154,C_155))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_605])).

tff(c_591,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k2_xboole_0(B_49,k4_xboole_0(A_48,B_49))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_110])).

tff(c_646,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k2_xboole_0(B_49,A_48)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_591])).

tff(c_10112,plain,(
    ! [C_156,B_157,C_158] : k4_xboole_0(C_156,k2_xboole_0(B_157,k2_xboole_0(C_158,C_156))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9697,c_646])).

tff(c_10263,plain,(
    ! [A_14,B_15,C_158] : k3_xboole_0(A_14,k4_xboole_0(B_15,k2_xboole_0(C_158,A_14))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_10112])).

tff(c_50762,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50606,c_10263])).

tff(c_50844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_50762])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.09/6.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.09/6.98  
% 13.09/6.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.09/6.99  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 13.09/6.99  
% 13.09/6.99  %Foreground sorts:
% 13.09/6.99  
% 13.09/6.99  
% 13.09/6.99  %Background operators:
% 13.09/6.99  
% 13.09/6.99  
% 13.09/6.99  %Foreground operators:
% 13.09/6.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.09/6.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.09/6.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.09/6.99  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.09/6.99  tff('#skF_2', type, '#skF_2': $i).
% 13.09/6.99  tff('#skF_3', type, '#skF_3': $i).
% 13.09/6.99  tff('#skF_1', type, '#skF_1': $i).
% 13.09/6.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.09/6.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.09/6.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.09/6.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.09/6.99  
% 13.09/7.00  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 13.09/7.00  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 13.09/7.00  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 13.09/7.00  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.09/7.00  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.09/7.00  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.09/7.00  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 13.09/7.00  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.09/7.00  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 13.09/7.00  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 13.09/7.00  tff(c_83, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.09/7.00  tff(c_22, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.09/7.00  tff(c_91, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_83, c_22])).
% 13.09/7.00  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.09/7.00  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.09/7.00  tff(c_92, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.09/7.00  tff(c_107, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_92])).
% 13.09/7.00  tff(c_110, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_107])).
% 13.09/7.00  tff(c_151, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.09/7.00  tff(c_160, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=k2_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_110, c_151])).
% 13.09/7.00  tff(c_570, plain, (![A_48, B_49, C_50]: (k4_xboole_0(k4_xboole_0(A_48, B_49), C_50)=k4_xboole_0(A_48, k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.09/7.00  tff(c_1349, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k2_xboole_0(B_65, k1_xboole_0))=k4_xboole_0(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_12, c_570])).
% 13.09/7.00  tff(c_1434, plain, (![A_64, A_8]: (k4_xboole_0(A_64, k2_xboole_0(A_8, A_8))=k4_xboole_0(A_64, A_8))), inference(superposition, [status(thm), theory('equality')], [c_160, c_1349])).
% 13.09/7.00  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.09/7.00  tff(c_24, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.09/7.00  tff(c_74, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.09/7.00  tff(c_78, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_74])).
% 13.09/7.00  tff(c_276, plain, (![A_37, B_38, C_39]: (k4_xboole_0(k3_xboole_0(A_37, B_38), C_39)=k3_xboole_0(A_37, k4_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.09/7.00  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.09/7.00  tff(c_7430, plain, (![C_133, A_134, B_135]: (k2_xboole_0(C_133, k3_xboole_0(A_134, k4_xboole_0(B_135, C_133)))=k2_xboole_0(C_133, k3_xboole_0(A_134, B_135)))), inference(superposition, [status(thm), theory('equality')], [c_276, c_10])).
% 13.09/7.00  tff(c_7676, plain, (k2_xboole_0('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78, c_7430])).
% 13.09/7.00  tff(c_7735, plain, (k2_xboole_0('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_7676])).
% 13.09/7.00  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.09/7.00  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.09/7.00  tff(c_617, plain, (![A_12, B_13, C_50]: (k4_xboole_0(A_12, k2_xboole_0(k3_xboole_0(A_12, B_13), C_50))=k4_xboole_0(k4_xboole_0(A_12, B_13), C_50))), inference(superposition, [status(thm), theory('equality')], [c_16, c_570])).
% 13.09/7.00  tff(c_4211, plain, (![A_105, B_106, C_107]: (k4_xboole_0(A_105, k2_xboole_0(k3_xboole_0(A_105, B_106), C_107))=k4_xboole_0(A_105, k2_xboole_0(B_106, C_107)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_617])).
% 13.09/7.00  tff(c_49859, plain, (![A_352, A_353, B_354]: (k4_xboole_0(A_352, k2_xboole_0(A_353, k3_xboole_0(A_352, B_354)))=k4_xboole_0(A_352, k2_xboole_0(B_354, A_353)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4211])).
% 13.09/7.00  tff(c_50353, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7735, c_49859])).
% 13.09/7.00  tff(c_50606, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1434, c_2, c_50353])).
% 13.09/7.00  tff(c_20, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k3_xboole_0(A_16, B_17), C_18)=k3_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.09/7.00  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.09/7.00  tff(c_631, plain, (![A_14, B_15, C_50]: (k4_xboole_0(A_14, k2_xboole_0(k4_xboole_0(A_14, B_15), C_50))=k4_xboole_0(k3_xboole_0(A_14, B_15), C_50))), inference(superposition, [status(thm), theory('equality')], [c_18, c_570])).
% 13.09/7.00  tff(c_654, plain, (![A_14, B_15, C_50]: (k4_xboole_0(A_14, k2_xboole_0(k4_xboole_0(A_14, B_15), C_50))=k3_xboole_0(A_14, k4_xboole_0(B_15, C_50)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_631])).
% 13.09/7.00  tff(c_605, plain, (![A_9, B_10, C_11, C_50]: (k4_xboole_0(k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)), C_50)=k4_xboole_0(k4_xboole_0(A_9, B_10), k2_xboole_0(C_11, C_50)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_570])).
% 13.09/7.00  tff(c_9697, plain, (![A_152, B_153, C_154, C_155]: (k4_xboole_0(A_152, k2_xboole_0(k2_xboole_0(B_153, C_154), C_155))=k4_xboole_0(A_152, k2_xboole_0(B_153, k2_xboole_0(C_154, C_155))))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_605])).
% 13.09/7.00  tff(c_591, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k2_xboole_0(B_49, k4_xboole_0(A_48, B_49)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_570, c_110])).
% 13.09/7.00  tff(c_646, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k2_xboole_0(B_49, A_48))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_591])).
% 13.09/7.00  tff(c_10112, plain, (![C_156, B_157, C_158]: (k4_xboole_0(C_156, k2_xboole_0(B_157, k2_xboole_0(C_158, C_156)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9697, c_646])).
% 13.09/7.00  tff(c_10263, plain, (![A_14, B_15, C_158]: (k3_xboole_0(A_14, k4_xboole_0(B_15, k2_xboole_0(C_158, A_14)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_654, c_10112])).
% 13.09/7.00  tff(c_50762, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_50606, c_10263])).
% 13.09/7.00  tff(c_50844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_50762])).
% 13.09/7.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.09/7.00  
% 13.09/7.00  Inference rules
% 13.09/7.00  ----------------------
% 13.09/7.00  #Ref     : 0
% 13.09/7.00  #Sup     : 12466
% 13.09/7.00  #Fact    : 0
% 13.09/7.00  #Define  : 0
% 13.09/7.00  #Split   : 0
% 13.09/7.00  #Chain   : 0
% 13.09/7.00  #Close   : 0
% 13.09/7.00  
% 13.09/7.00  Ordering : KBO
% 13.09/7.00  
% 13.09/7.00  Simplification rules
% 13.09/7.00  ----------------------
% 13.09/7.00  #Subsume      : 98
% 13.09/7.00  #Demod        : 17480
% 13.09/7.00  #Tautology    : 8726
% 13.09/7.00  #SimpNegUnit  : 1
% 13.09/7.00  #BackRed      : 9
% 13.09/7.00  
% 13.09/7.00  #Partial instantiations: 0
% 13.09/7.00  #Strategies tried      : 1
% 13.09/7.00  
% 13.09/7.00  Timing (in seconds)
% 13.09/7.00  ----------------------
% 13.09/7.00  Preprocessing        : 0.28
% 13.09/7.00  Parsing              : 0.16
% 13.09/7.00  CNF conversion       : 0.01
% 13.09/7.00  Main loop            : 5.95
% 13.09/7.00  Inferencing          : 0.86
% 13.09/7.00  Reduction            : 3.84
% 13.09/7.00  Demodulation         : 3.55
% 13.09/7.00  BG Simplification    : 0.10
% 13.09/7.00  Subsumption          : 0.93
% 13.09/7.00  Abstraction          : 0.20
% 13.09/7.00  MUC search           : 0.00
% 13.09/7.00  Cooper               : 0.00
% 13.09/7.00  Total                : 6.27
% 13.09/7.00  Index Insertion      : 0.00
% 13.09/7.00  Index Deletion       : 0.00
% 13.09/7.00  Index Matching       : 0.00
% 13.09/7.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
