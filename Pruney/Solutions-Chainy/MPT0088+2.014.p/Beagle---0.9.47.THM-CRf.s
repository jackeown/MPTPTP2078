%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:21 EST 2020

% Result     : Theorem 7.10s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 177 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :   61 ( 172 expanded)
%              Number of equality atoms :   53 ( 161 expanded)
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

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_88,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_22])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_363,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k4_xboole_0(A_38,B_39),C_40) = k4_xboole_0(A_38,k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_285,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_320,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_285])).

tff(c_327,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_320])).

tff(c_373,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(B_39,k4_xboole_0(A_38,B_39))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_327])).

tff(c_426,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(B_39,A_38)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_373])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [A_28,B_29] : k2_xboole_0(k3_xboole_0(A_28,B_29),k4_xboole_0(A_28,B_29)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_5,k1_xboole_0)) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_142])).

tff(c_169,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_163])).

tff(c_18,plain,(
    ! [A_14,B_15] : k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_522,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k2_xboole_0(B_45,A_44)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_373])).

tff(c_572,plain,(
    ! [A_14,B_15] : k4_xboole_0(k4_xboole_0(A_14,B_15),A_14) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_522])).

tff(c_2299,plain,(
    ! [A_83,B_84] : k2_xboole_0(k3_xboole_0(A_83,k4_xboole_0(A_83,B_84)),k3_xboole_0(A_83,B_84)) = A_83 ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_18])).

tff(c_2368,plain,(
    ! [A_14,B_15] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_14,B_15),k1_xboole_0),k3_xboole_0(k4_xboole_0(A_14,B_15),A_14)) = k4_xboole_0(A_14,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_2299])).

tff(c_2431,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_2,c_8,c_2368])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_288,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,k4_xboole_0(A_35,B_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_16])).

tff(c_3119,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k4_xboole_0(A_35,B_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_288])).

tff(c_328,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_320])).

tff(c_333,plain,(
    ! [A_37] : k4_xboole_0(A_37,k1_xboole_0) = k3_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_16])).

tff(c_435,plain,(
    ! [A_41] : k3_xboole_0(A_41,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_333])).

tff(c_441,plain,(
    ! [A_41] : k2_xboole_0(A_41,k4_xboole_0(A_41,A_41)) = A_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_18])).

tff(c_462,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_xboole_0) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_441])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_129,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = k1_xboole_0
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_129])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_xboole_0(k4_xboole_0(A_9,B_10),C_11) = k4_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_704,plain,(
    ! [A_49,B_50,C_51] : k2_xboole_0(k4_xboole_0(A_49,B_50),k3_xboole_0(A_49,C_51)) = k4_xboole_0(A_49,k4_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_738,plain,(
    ! [A_12,B_13,C_51] : k4_xboole_0(A_12,k4_xboole_0(k4_xboole_0(A_12,B_13),C_51)) = k2_xboole_0(k3_xboole_0(A_12,B_13),k3_xboole_0(A_12,C_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_704])).

tff(c_8263,plain,(
    ! [A_149,B_150,C_151] : k2_xboole_0(k3_xboole_0(A_149,B_150),k3_xboole_0(A_149,C_151)) = k3_xboole_0(A_149,k2_xboole_0(B_150,C_151)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_738])).

tff(c_8455,plain,(
    ! [B_150] : k3_xboole_0('#skF_1',k2_xboole_0(B_150,k4_xboole_0('#skF_2','#skF_3'))) = k2_xboole_0(k3_xboole_0('#skF_1',B_150),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_8263])).

tff(c_9620,plain,(
    ! [B_161] : k3_xboole_0('#skF_1',k2_xboole_0(B_161,k4_xboole_0('#skF_2','#skF_3'))) = k3_xboole_0('#skF_1',B_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_8455])).

tff(c_9766,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_9620])).

tff(c_9941,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_3')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9766,c_3119])).

tff(c_9979,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3119,c_9941])).

tff(c_410,plain,(
    ! [A_38,B_39,B_13] : k4_xboole_0(A_38,k2_xboole_0(B_39,k4_xboole_0(k4_xboole_0(A_38,B_39),B_13))) = k3_xboole_0(k4_xboole_0(A_38,B_39),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_363])).

tff(c_13838,plain,(
    ! [A_191,B_192,B_193] : k4_xboole_0(A_191,k2_xboole_0(B_192,k4_xboole_0(A_191,k2_xboole_0(B_192,B_193)))) = k3_xboole_0(k4_xboole_0(A_191,B_192),B_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_410])).

tff(c_14009,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_3'))) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9979,c_13838])).

tff(c_14232,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_10,c_2,c_14009])).

tff(c_14234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_14232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:19:21 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.10/2.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.71  
% 7.31/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.72  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.31/2.72  
% 7.31/2.72  %Foreground sorts:
% 7.31/2.72  
% 7.31/2.72  
% 7.31/2.72  %Background operators:
% 7.31/2.72  
% 7.31/2.72  
% 7.31/2.72  %Foreground operators:
% 7.31/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.31/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.31/2.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.31/2.72  tff('#skF_2', type, '#skF_2': $i).
% 7.31/2.72  tff('#skF_3', type, '#skF_3': $i).
% 7.31/2.72  tff('#skF_1', type, '#skF_1': $i).
% 7.31/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.31/2.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.31/2.72  
% 7.31/2.73  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.31/2.73  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 7.31/2.73  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.31/2.73  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.31/2.73  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 7.31/2.73  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.31/2.73  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.31/2.73  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.31/2.73  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 7.31/2.73  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 7.31/2.73  tff(c_88, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.31/2.73  tff(c_22, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.31/2.73  tff(c_92, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_22])).
% 7.31/2.73  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.31/2.73  tff(c_363, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k4_xboole_0(A_38, B_39), C_40)=k4_xboole_0(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.31/2.73  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.31/2.73  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.31/2.73  tff(c_285, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.31/2.73  tff(c_320, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_285])).
% 7.31/2.73  tff(c_327, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_320])).
% 7.31/2.73  tff(c_373, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(B_39, k4_xboole_0(A_38, B_39)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_363, c_327])).
% 7.31/2.73  tff(c_426, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(B_39, A_38))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_373])).
% 7.31/2.73  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.31/2.73  tff(c_142, plain, (![A_28, B_29]: (k2_xboole_0(k3_xboole_0(A_28, B_29), k4_xboole_0(A_28, B_29))=A_28)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.31/2.73  tff(c_163, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_5, k1_xboole_0))=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_142])).
% 7.31/2.73  tff(c_169, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_163])).
% 7.31/2.73  tff(c_18, plain, (![A_14, B_15]: (k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.31/2.73  tff(c_522, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k2_xboole_0(B_45, A_44))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_373])).
% 7.31/2.73  tff(c_572, plain, (![A_14, B_15]: (k4_xboole_0(k4_xboole_0(A_14, B_15), A_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_522])).
% 7.31/2.73  tff(c_2299, plain, (![A_83, B_84]: (k2_xboole_0(k3_xboole_0(A_83, k4_xboole_0(A_83, B_84)), k3_xboole_0(A_83, B_84))=A_83)), inference(superposition, [status(thm), theory('equality')], [c_285, c_18])).
% 7.31/2.73  tff(c_2368, plain, (![A_14, B_15]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_14, B_15), k1_xboole_0), k3_xboole_0(k4_xboole_0(A_14, B_15), A_14))=k4_xboole_0(A_14, B_15))), inference(superposition, [status(thm), theory('equality')], [c_572, c_2299])).
% 7.31/2.73  tff(c_2431, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_2, c_8, c_2368])).
% 7.31/2.73  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.31/2.73  tff(c_288, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k3_xboole_0(A_35, k4_xboole_0(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_285, c_16])).
% 7.31/2.73  tff(c_3119, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k4_xboole_0(A_35, B_36))), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_288])).
% 7.31/2.73  tff(c_328, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_320])).
% 7.31/2.73  tff(c_333, plain, (![A_37]: (k4_xboole_0(A_37, k1_xboole_0)=k3_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_328, c_16])).
% 7.31/2.73  tff(c_435, plain, (![A_41]: (k3_xboole_0(A_41, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_333])).
% 7.31/2.73  tff(c_441, plain, (![A_41]: (k2_xboole_0(A_41, k4_xboole_0(A_41, A_41))=A_41)), inference(superposition, [status(thm), theory('equality')], [c_435, c_18])).
% 7.31/2.73  tff(c_462, plain, (![A_41]: (k2_xboole_0(A_41, k1_xboole_0)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_441])).
% 7.31/2.73  tff(c_24, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.31/2.73  tff(c_129, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=k1_xboole_0 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.31/2.73  tff(c_137, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_129])).
% 7.31/2.73  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_xboole_0(k4_xboole_0(A_9, B_10), C_11)=k4_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.31/2.73  tff(c_704, plain, (![A_49, B_50, C_51]: (k2_xboole_0(k4_xboole_0(A_49, B_50), k3_xboole_0(A_49, C_51))=k4_xboole_0(A_49, k4_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.31/2.73  tff(c_738, plain, (![A_12, B_13, C_51]: (k4_xboole_0(A_12, k4_xboole_0(k4_xboole_0(A_12, B_13), C_51))=k2_xboole_0(k3_xboole_0(A_12, B_13), k3_xboole_0(A_12, C_51)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_704])).
% 7.31/2.73  tff(c_8263, plain, (![A_149, B_150, C_151]: (k2_xboole_0(k3_xboole_0(A_149, B_150), k3_xboole_0(A_149, C_151))=k3_xboole_0(A_149, k2_xboole_0(B_150, C_151)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_738])).
% 7.31/2.73  tff(c_8455, plain, (![B_150]: (k3_xboole_0('#skF_1', k2_xboole_0(B_150, k4_xboole_0('#skF_2', '#skF_3')))=k2_xboole_0(k3_xboole_0('#skF_1', B_150), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_137, c_8263])).
% 7.31/2.73  tff(c_9620, plain, (![B_161]: (k3_xboole_0('#skF_1', k2_xboole_0(B_161, k4_xboole_0('#skF_2', '#skF_3')))=k3_xboole_0('#skF_1', B_161))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_8455])).
% 7.31/2.73  tff(c_9766, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_9620])).
% 7.31/2.73  tff(c_9941, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9766, c_3119])).
% 7.31/2.73  tff(c_9979, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3119, c_9941])).
% 7.31/2.73  tff(c_410, plain, (![A_38, B_39, B_13]: (k4_xboole_0(A_38, k2_xboole_0(B_39, k4_xboole_0(k4_xboole_0(A_38, B_39), B_13)))=k3_xboole_0(k4_xboole_0(A_38, B_39), B_13))), inference(superposition, [status(thm), theory('equality')], [c_16, c_363])).
% 7.31/2.73  tff(c_13838, plain, (![A_191, B_192, B_193]: (k4_xboole_0(A_191, k2_xboole_0(B_192, k4_xboole_0(A_191, k2_xboole_0(B_192, B_193))))=k3_xboole_0(k4_xboole_0(A_191, B_192), B_193))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_410])).
% 7.31/2.73  tff(c_14009, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_3')))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9979, c_13838])).
% 7.31/2.73  tff(c_14232, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_426, c_10, c_2, c_14009])).
% 7.31/2.73  tff(c_14234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_14232])).
% 7.31/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.31/2.73  
% 7.31/2.73  Inference rules
% 7.31/2.73  ----------------------
% 7.31/2.73  #Ref     : 0
% 7.31/2.73  #Sup     : 3604
% 7.31/2.73  #Fact    : 0
% 7.31/2.73  #Define  : 0
% 7.31/2.73  #Split   : 0
% 7.31/2.73  #Chain   : 0
% 7.31/2.73  #Close   : 0
% 7.31/2.73  
% 7.31/2.73  Ordering : KBO
% 7.31/2.73  
% 7.31/2.73  Simplification rules
% 7.31/2.73  ----------------------
% 7.31/2.73  #Subsume      : 6
% 7.31/2.73  #Demod        : 3624
% 7.31/2.73  #Tautology    : 2344
% 7.31/2.73  #SimpNegUnit  : 1
% 7.31/2.73  #BackRed      : 3
% 7.31/2.73  
% 7.31/2.73  #Partial instantiations: 0
% 7.31/2.73  #Strategies tried      : 1
% 7.31/2.73  
% 7.31/2.73  Timing (in seconds)
% 7.31/2.73  ----------------------
% 7.31/2.73  Preprocessing        : 0.28
% 7.31/2.73  Parsing              : 0.16
% 7.31/2.73  CNF conversion       : 0.02
% 7.31/2.73  Main loop            : 1.69
% 7.31/2.73  Inferencing          : 0.42
% 7.31/2.73  Reduction            : 0.91
% 7.31/2.73  Demodulation         : 0.79
% 7.31/2.73  BG Simplification    : 0.05
% 7.31/2.73  Subsumption          : 0.23
% 7.31/2.73  Abstraction          : 0.08
% 7.31/2.73  MUC search           : 0.00
% 7.31/2.73  Cooper               : 0.00
% 7.31/2.73  Total                : 2.01
% 7.31/2.73  Index Insertion      : 0.00
% 7.31/2.73  Index Deletion       : 0.00
% 7.31/2.73  Index Matching       : 0.00
% 7.31/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
