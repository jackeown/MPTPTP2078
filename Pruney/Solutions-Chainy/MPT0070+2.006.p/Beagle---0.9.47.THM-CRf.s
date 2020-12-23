%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:18 EST 2020

% Result     : Theorem 8.65s
% Output     : CNFRefutation 8.81s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 102 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :   61 ( 106 expanded)
%              Number of equality atoms :   47 (  79 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(c_180,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_188,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_180,c_24])).

tff(c_14,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_212,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_224,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_212])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_175,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_179,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_175])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_441,plain,(
    ! [A_49,B_50] : k3_xboole_0(k4_xboole_0(A_49,B_50),A_49) = k4_xboole_0(A_49,B_50) ),
    inference(resolution,[status(thm)],[c_16,c_212])).

tff(c_480,plain,(
    ! [A_3,B_50] : k3_xboole_0(A_3,k4_xboole_0(A_3,B_50)) = k4_xboole_0(A_3,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_441])).

tff(c_258,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_261,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,k4_xboole_0(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_22])).

tff(c_1399,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_261])).

tff(c_1466,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_1399])).

tff(c_1498,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1466])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k4_xboole_0(A_15,B_16),C_17) = k4_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2141,plain,(
    ! [C_90] : k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_90)) = k4_xboole_0('#skF_2',C_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_20])).

tff(c_17319,plain,(
    ! [A_282] : k4_xboole_0('#skF_2',k2_xboole_0(A_282,'#skF_3')) = k4_xboole_0('#skF_2',A_282) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2141])).

tff(c_276,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_258])).

tff(c_279,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_276])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_345,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k4_xboole_0(A_44,B_45),C_46) = k4_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4108,plain,(
    ! [A_128,B_129,C_130] : k4_xboole_0(k4_xboole_0(A_128,B_129),k4_xboole_0(A_128,k2_xboole_0(B_129,C_130))) = k3_xboole_0(k4_xboole_0(A_128,B_129),C_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_22])).

tff(c_4309,plain,(
    ! [A_128,A_7] : k4_xboole_0(k4_xboole_0(A_128,A_7),k4_xboole_0(A_128,A_7)) = k3_xboole_0(k4_xboole_0(A_128,A_7),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_4108])).

tff(c_4369,plain,(
    ! [A_131,A_132] : k3_xboole_0(A_131,k4_xboole_0(A_132,A_131)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_4,c_4309])).

tff(c_4504,plain,(
    ! [C_17,A_15,B_16] : k3_xboole_0(C_17,k4_xboole_0(A_15,k2_xboole_0(B_16,C_17))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4369])).

tff(c_17487,plain,(
    ! [A_283] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',A_283)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_17319,c_4504])).

tff(c_17854,plain,(
    ! [B_285] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_2',B_285)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_17487])).

tff(c_18264,plain,(
    ! [A_287] : k3_xboole_0('#skF_3',k3_xboole_0(A_287,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_17854])).

tff(c_18405,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_18264])).

tff(c_472,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(k3_xboole_0(A_18,B_19),A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_441])).

tff(c_7458,plain,(
    ! [A_194,B_195] : k3_xboole_0(A_194,k3_xboole_0(A_194,B_195)) = k3_xboole_0(A_194,B_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4,c_472])).

tff(c_7627,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k3_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7458])).

tff(c_18468,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18405,c_7627])).

tff(c_18575,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18468])).

tff(c_18577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_18575])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.65/3.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.65/3.39  
% 8.65/3.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.65/3.39  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.65/3.39  
% 8.65/3.39  %Foreground sorts:
% 8.65/3.39  
% 8.65/3.39  
% 8.65/3.39  %Background operators:
% 8.65/3.39  
% 8.65/3.39  
% 8.65/3.39  %Foreground operators:
% 8.65/3.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.65/3.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.65/3.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.65/3.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.65/3.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.65/3.39  tff('#skF_2', type, '#skF_2': $i).
% 8.65/3.39  tff('#skF_3', type, '#skF_3': $i).
% 8.65/3.39  tff('#skF_1', type, '#skF_1': $i).
% 8.65/3.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.65/3.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.65/3.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.65/3.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.81/3.39  
% 8.81/3.41  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.81/3.41  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 8.81/3.41  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 8.81/3.41  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.81/3.41  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.81/3.41  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.81/3.41  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.81/3.41  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.81/3.41  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.81/3.41  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.81/3.41  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 8.81/3.41  tff(c_180, plain, (![A_33, B_34]: (r1_xboole_0(A_33, B_34) | k3_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.81/3.41  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.81/3.41  tff(c_188, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_180, c_24])).
% 8.81/3.41  tff(c_14, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.81/3.41  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.81/3.41  tff(c_212, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.81/3.41  tff(c_224, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_28, c_212])).
% 8.81/3.41  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.81/3.41  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.81/3.41  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.81/3.41  tff(c_18, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.81/3.41  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.81/3.41  tff(c_175, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.81/3.41  tff(c_179, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_175])).
% 8.81/3.41  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.81/3.41  tff(c_441, plain, (![A_49, B_50]: (k3_xboole_0(k4_xboole_0(A_49, B_50), A_49)=k4_xboole_0(A_49, B_50))), inference(resolution, [status(thm)], [c_16, c_212])).
% 8.81/3.41  tff(c_480, plain, (![A_3, B_50]: (k3_xboole_0(A_3, k4_xboole_0(A_3, B_50))=k4_xboole_0(A_3, B_50))), inference(superposition, [status(thm), theory('equality')], [c_4, c_441])).
% 8.81/3.41  tff(c_258, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.81/3.41  tff(c_261, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k3_xboole_0(A_38, k4_xboole_0(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_258, c_22])).
% 8.81/3.41  tff(c_1399, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_261])).
% 8.81/3.41  tff(c_1466, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_179, c_1399])).
% 8.81/3.41  tff(c_1498, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1466])).
% 8.81/3.41  tff(c_20, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k4_xboole_0(A_15, B_16), C_17)=k4_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.81/3.41  tff(c_2141, plain, (![C_90]: (k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_90))=k4_xboole_0('#skF_2', C_90))), inference(superposition, [status(thm), theory('equality')], [c_1498, c_20])).
% 8.81/3.41  tff(c_17319, plain, (![A_282]: (k4_xboole_0('#skF_2', k2_xboole_0(A_282, '#skF_3'))=k4_xboole_0('#skF_2', A_282))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2141])).
% 8.81/3.41  tff(c_276, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_258])).
% 8.81/3.41  tff(c_279, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_276])).
% 8.81/3.41  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.81/3.41  tff(c_345, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), C_46)=k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.81/3.41  tff(c_4108, plain, (![A_128, B_129, C_130]: (k4_xboole_0(k4_xboole_0(A_128, B_129), k4_xboole_0(A_128, k2_xboole_0(B_129, C_130)))=k3_xboole_0(k4_xboole_0(A_128, B_129), C_130))), inference(superposition, [status(thm), theory('equality')], [c_345, c_22])).
% 8.81/3.41  tff(c_4309, plain, (![A_128, A_7]: (k4_xboole_0(k4_xboole_0(A_128, A_7), k4_xboole_0(A_128, A_7))=k3_xboole_0(k4_xboole_0(A_128, A_7), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_4108])).
% 8.81/3.41  tff(c_4369, plain, (![A_131, A_132]: (k3_xboole_0(A_131, k4_xboole_0(A_132, A_131))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_279, c_4, c_4309])).
% 8.81/3.41  tff(c_4504, plain, (![C_17, A_15, B_16]: (k3_xboole_0(C_17, k4_xboole_0(A_15, k2_xboole_0(B_16, C_17)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_4369])).
% 8.81/3.41  tff(c_17487, plain, (![A_283]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', A_283))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_17319, c_4504])).
% 8.81/3.41  tff(c_17854, plain, (![B_285]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_2', B_285))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_17487])).
% 8.81/3.41  tff(c_18264, plain, (![A_287]: (k3_xboole_0('#skF_3', k3_xboole_0(A_287, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_17854])).
% 8.81/3.41  tff(c_18405, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_224, c_18264])).
% 8.81/3.41  tff(c_472, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(k3_xboole_0(A_18, B_19), A_18))), inference(superposition, [status(thm), theory('equality')], [c_22, c_441])).
% 8.81/3.41  tff(c_7458, plain, (![A_194, B_195]: (k3_xboole_0(A_194, k3_xboole_0(A_194, B_195))=k3_xboole_0(A_194, B_195))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4, c_472])).
% 8.81/3.41  tff(c_7627, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k3_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7458])).
% 8.81/3.41  tff(c_18468, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18405, c_7627])).
% 8.81/3.41  tff(c_18575, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18468])).
% 8.81/3.41  tff(c_18577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_18575])).
% 8.81/3.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.81/3.41  
% 8.81/3.41  Inference rules
% 8.81/3.41  ----------------------
% 8.81/3.41  #Ref     : 0
% 8.81/3.41  #Sup     : 4465
% 8.81/3.41  #Fact    : 0
% 8.81/3.41  #Define  : 0
% 8.81/3.41  #Split   : 0
% 8.81/3.41  #Chain   : 0
% 8.81/3.41  #Close   : 0
% 8.81/3.41  
% 8.81/3.41  Ordering : KBO
% 8.81/3.41  
% 8.81/3.41  Simplification rules
% 8.81/3.41  ----------------------
% 8.81/3.41  #Subsume      : 16
% 8.81/3.41  #Demod        : 5324
% 8.81/3.41  #Tautology    : 3435
% 8.81/3.41  #SimpNegUnit  : 1
% 8.81/3.41  #BackRed      : 15
% 8.81/3.41  
% 8.81/3.41  #Partial instantiations: 0
% 8.81/3.41  #Strategies tried      : 1
% 8.81/3.41  
% 8.81/3.41  Timing (in seconds)
% 8.81/3.41  ----------------------
% 8.81/3.41  Preprocessing        : 0.30
% 8.81/3.41  Parsing              : 0.18
% 8.81/3.41  CNF conversion       : 0.02
% 8.81/3.41  Main loop            : 2.30
% 8.81/3.41  Inferencing          : 0.49
% 8.81/3.41  Reduction            : 1.30
% 8.81/3.41  Demodulation         : 1.15
% 8.81/3.41  BG Simplification    : 0.05
% 8.81/3.41  Subsumption          : 0.34
% 8.81/3.41  Abstraction          : 0.09
% 8.81/3.41  MUC search           : 0.00
% 8.81/3.41  Cooper               : 0.00
% 8.81/3.41  Total                : 2.63
% 8.81/3.41  Index Insertion      : 0.00
% 8.81/3.41  Index Deletion       : 0.00
% 8.81/3.41  Index Matching       : 0.00
% 8.81/3.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
