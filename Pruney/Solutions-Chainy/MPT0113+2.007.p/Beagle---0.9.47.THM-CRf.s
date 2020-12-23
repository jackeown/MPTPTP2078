%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:12 EST 2020

% Result     : Theorem 6.57s
% Output     : CNFRefutation 6.57s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 126 expanded)
%              Number of leaves         :   27 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 161 expanded)
%              Number of equality atoms :   42 (  64 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_24,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_61,plain,(
    ! [A_30,B_31] : r1_tarski(k4_xboole_0(A_30,B_31),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    ! [A_21] : r1_tarski(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_61])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3648,plain,(
    ! [A_178,B_179] :
      ( k3_xboole_0(A_178,B_179) = k1_xboole_0
      | ~ r1_xboole_0(A_178,B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3660,plain,(
    ! [A_22] : k3_xboole_0(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_3648])).

tff(c_3744,plain,(
    ! [A_187,B_188] : k5_xboole_0(A_187,k3_xboole_0(A_187,B_188)) = k4_xboole_0(A_187,B_188) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3756,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = k4_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_3744])).

tff(c_3768,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3756])).

tff(c_4023,plain,(
    ! [A_203,C_204,B_205] :
      ( r1_xboole_0(A_203,k4_xboole_0(C_204,B_205))
      | ~ r1_tarski(A_203,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4502,plain,(
    ! [A_240,C_241,B_242] :
      ( k3_xboole_0(A_240,k4_xboole_0(C_241,B_242)) = k1_xboole_0
      | ~ r1_tarski(A_240,B_242) ) ),
    inference(resolution,[status(thm)],[c_4023,c_4])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4512,plain,(
    ! [A_240,C_241,B_242] :
      ( k4_xboole_0(A_240,k4_xboole_0(C_241,B_242)) = k5_xboole_0(A_240,k1_xboole_0)
      | ~ r1_tarski(A_240,B_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4502,c_12])).

tff(c_4668,plain,(
    ! [A_246,C_247,B_248] :
      ( k4_xboole_0(A_246,k4_xboole_0(C_247,B_248)) = A_246
      | ~ r1_tarski(A_246,B_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3768,c_4512])).

tff(c_28,plain,(
    ! [A_23,C_25,B_24] :
      ( r1_xboole_0(A_23,k4_xboole_0(C_25,B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12711,plain,(
    ! [A_373,A_374,C_375,B_376] :
      ( r1_xboole_0(A_373,A_374)
      | ~ r1_tarski(A_373,k4_xboole_0(C_375,B_376))
      | ~ r1_tarski(A_374,B_376) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4668,c_28])).

tff(c_12776,plain,(
    ! [A_377] :
      ( r1_xboole_0('#skF_1',A_377)
      | ~ r1_tarski(A_377,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_12711])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_150,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_279,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_xboole_0(A_52,k4_xboole_0(C_53,B_54))
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_923,plain,(
    ! [C_100,B_101,A_102] :
      ( r1_xboole_0(k4_xboole_0(C_100,B_101),A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(resolution,[status(thm)],[c_279,c_10])).

tff(c_2479,plain,(
    ! [C_146,B_147,A_148] :
      ( k3_xboole_0(k4_xboole_0(C_146,B_147),A_148) = k1_xboole_0
      | ~ r1_tarski(A_148,B_147) ) ),
    inference(resolution,[status(thm)],[c_923,c_4])).

tff(c_222,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_234,plain,(
    ! [A_17,B_18] : k3_xboole_0(k4_xboole_0(A_17,B_18),A_17) = k4_xboole_0(A_17,B_18) ),
    inference(resolution,[status(thm)],[c_20,c_222])).

tff(c_2608,plain,(
    ! [A_149,B_150] :
      ( k4_xboole_0(A_149,B_150) = k1_xboole_0
      | ~ r1_tarski(A_149,B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2479,c_234])).

tff(c_2662,plain,(
    ! [A_151,B_152] : k4_xboole_0(k4_xboole_0(A_151,B_152),A_151) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_2608])).

tff(c_22,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2698,plain,(
    ! [A_151,B_152] : k2_xboole_0(A_151,k4_xboole_0(A_151,B_152)) = k2_xboole_0(A_151,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2662,c_22])).

tff(c_2754,plain,(
    ! [A_151,B_152] : k2_xboole_0(A_151,k4_xboole_0(A_151,B_152)) = A_151 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2698])).

tff(c_1351,plain,(
    ! [A_119,C_120,B_121] :
      ( k3_xboole_0(A_119,k4_xboole_0(C_120,B_121)) = k1_xboole_0
      | ~ r1_tarski(A_119,B_121) ) ),
    inference(resolution,[status(thm)],[c_279,c_4])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2021,plain,(
    ! [C_136,B_137] :
      ( k4_xboole_0(C_136,B_137) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_136,B_137),B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1351,c_8])).

tff(c_2055,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_2021])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_248,plain,(
    ! [A_49,B_50] : k5_xboole_0(A_49,k3_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_266,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_248])).

tff(c_235,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_222])).

tff(c_257,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_248])).

tff(c_325,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_257])).

tff(c_385,plain,(
    ! [A_65,B_66] : k2_xboole_0(A_65,k4_xboole_0(B_66,A_65)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_401,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1','#skF_1')) = k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_385])).

tff(c_413,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1','#skF_1')) = k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_401])).

tff(c_3440,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2055,c_413])).

tff(c_416,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(A_67,C_68)
      | ~ r1_tarski(k2_xboole_0(A_67,B_69),C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_437,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,C_71)
      | ~ r1_tarski(k2_xboole_0(B_72,A_70),C_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_416])).

tff(c_506,plain,(
    ! [A_76,B_77] : r1_tarski(A_76,k2_xboole_0(B_77,A_76)) ),
    inference(resolution,[status(thm)],[c_64,c_437])).

tff(c_14,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(A_11,C_13)
      | ~ r1_tarski(k2_xboole_0(A_11,B_12),C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_534,plain,(
    ! [A_11,B_77,B_12] : r1_tarski(A_11,k2_xboole_0(B_77,k2_xboole_0(A_11,B_12))) ),
    inference(resolution,[status(thm)],[c_506,c_14])).

tff(c_3562,plain,(
    ! [B_170] : r1_tarski('#skF_1',k2_xboole_0(B_170,k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3440,c_534])).

tff(c_3574,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2754,c_3562])).

tff(c_3599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_3574])).

tff(c_3600,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_12784,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_12776,c_3600])).

tff(c_12790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_12784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.57/2.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.57/2.43  
% 6.57/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.57/2.44  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.57/2.44  
% 6.57/2.44  %Foreground sorts:
% 6.57/2.44  
% 6.57/2.44  
% 6.57/2.44  %Background operators:
% 6.57/2.44  
% 6.57/2.44  
% 6.57/2.44  %Foreground operators:
% 6.57/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.57/2.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.57/2.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.57/2.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.57/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.57/2.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.57/2.44  tff('#skF_2', type, '#skF_2': $i).
% 6.57/2.44  tff('#skF_3', type, '#skF_3': $i).
% 6.57/2.44  tff('#skF_1', type, '#skF_1': $i).
% 6.57/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.57/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.57/2.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.57/2.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.57/2.44  
% 6.57/2.45  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.57/2.45  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.57/2.45  tff(f_68, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.57/2.45  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.57/2.45  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.57/2.45  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.57/2.45  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 6.57/2.45  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.57/2.45  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.57/2.45  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.57/2.45  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.57/2.45  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.57/2.45  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.57/2.45  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.57/2.45  tff(c_24, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.57/2.45  tff(c_61, plain, (![A_30, B_31]: (r1_tarski(k4_xboole_0(A_30, B_31), A_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.57/2.45  tff(c_64, plain, (![A_21]: (r1_tarski(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_24, c_61])).
% 6.57/2.45  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.57/2.45  tff(c_26, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.57/2.45  tff(c_3648, plain, (![A_178, B_179]: (k3_xboole_0(A_178, B_179)=k1_xboole_0 | ~r1_xboole_0(A_178, B_179))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.57/2.45  tff(c_3660, plain, (![A_22]: (k3_xboole_0(A_22, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_3648])).
% 6.57/2.45  tff(c_3744, plain, (![A_187, B_188]: (k5_xboole_0(A_187, k3_xboole_0(A_187, B_188))=k4_xboole_0(A_187, B_188))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.57/2.45  tff(c_3756, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=k4_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3660, c_3744])).
% 6.57/2.45  tff(c_3768, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3756])).
% 6.57/2.45  tff(c_4023, plain, (![A_203, C_204, B_205]: (r1_xboole_0(A_203, k4_xboole_0(C_204, B_205)) | ~r1_tarski(A_203, B_205))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.57/2.45  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.57/2.45  tff(c_4502, plain, (![A_240, C_241, B_242]: (k3_xboole_0(A_240, k4_xboole_0(C_241, B_242))=k1_xboole_0 | ~r1_tarski(A_240, B_242))), inference(resolution, [status(thm)], [c_4023, c_4])).
% 6.57/2.45  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.57/2.45  tff(c_4512, plain, (![A_240, C_241, B_242]: (k4_xboole_0(A_240, k4_xboole_0(C_241, B_242))=k5_xboole_0(A_240, k1_xboole_0) | ~r1_tarski(A_240, B_242))), inference(superposition, [status(thm), theory('equality')], [c_4502, c_12])).
% 6.57/2.45  tff(c_4668, plain, (![A_246, C_247, B_248]: (k4_xboole_0(A_246, k4_xboole_0(C_247, B_248))=A_246 | ~r1_tarski(A_246, B_248))), inference(demodulation, [status(thm), theory('equality')], [c_3768, c_4512])).
% 6.57/2.45  tff(c_28, plain, (![A_23, C_25, B_24]: (r1_xboole_0(A_23, k4_xboole_0(C_25, B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.57/2.45  tff(c_12711, plain, (![A_373, A_374, C_375, B_376]: (r1_xboole_0(A_373, A_374) | ~r1_tarski(A_373, k4_xboole_0(C_375, B_376)) | ~r1_tarski(A_374, B_376))), inference(superposition, [status(thm), theory('equality')], [c_4668, c_28])).
% 6.57/2.45  tff(c_12776, plain, (![A_377]: (r1_xboole_0('#skF_1', A_377) | ~r1_tarski(A_377, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_12711])).
% 6.57/2.45  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.57/2.45  tff(c_150, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 6.57/2.45  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.57/2.45  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.57/2.45  tff(c_279, plain, (![A_52, C_53, B_54]: (r1_xboole_0(A_52, k4_xboole_0(C_53, B_54)) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.57/2.45  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.57/2.45  tff(c_923, plain, (![C_100, B_101, A_102]: (r1_xboole_0(k4_xboole_0(C_100, B_101), A_102) | ~r1_tarski(A_102, B_101))), inference(resolution, [status(thm)], [c_279, c_10])).
% 6.57/2.45  tff(c_2479, plain, (![C_146, B_147, A_148]: (k3_xboole_0(k4_xboole_0(C_146, B_147), A_148)=k1_xboole_0 | ~r1_tarski(A_148, B_147))), inference(resolution, [status(thm)], [c_923, c_4])).
% 6.57/2.45  tff(c_222, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.57/2.45  tff(c_234, plain, (![A_17, B_18]: (k3_xboole_0(k4_xboole_0(A_17, B_18), A_17)=k4_xboole_0(A_17, B_18))), inference(resolution, [status(thm)], [c_20, c_222])).
% 6.57/2.45  tff(c_2608, plain, (![A_149, B_150]: (k4_xboole_0(A_149, B_150)=k1_xboole_0 | ~r1_tarski(A_149, B_150))), inference(superposition, [status(thm), theory('equality')], [c_2479, c_234])).
% 6.57/2.45  tff(c_2662, plain, (![A_151, B_152]: (k4_xboole_0(k4_xboole_0(A_151, B_152), A_151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_2608])).
% 6.57/2.45  tff(c_22, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.57/2.45  tff(c_2698, plain, (![A_151, B_152]: (k2_xboole_0(A_151, k4_xboole_0(A_151, B_152))=k2_xboole_0(A_151, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2662, c_22])).
% 6.57/2.45  tff(c_2754, plain, (![A_151, B_152]: (k2_xboole_0(A_151, k4_xboole_0(A_151, B_152))=A_151)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2698])).
% 6.57/2.45  tff(c_1351, plain, (![A_119, C_120, B_121]: (k3_xboole_0(A_119, k4_xboole_0(C_120, B_121))=k1_xboole_0 | ~r1_tarski(A_119, B_121))), inference(resolution, [status(thm)], [c_279, c_4])).
% 6.57/2.45  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.57/2.45  tff(c_2021, plain, (![C_136, B_137]: (k4_xboole_0(C_136, B_137)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_136, B_137), B_137))), inference(superposition, [status(thm), theory('equality')], [c_1351, c_8])).
% 6.57/2.45  tff(c_2055, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_2021])).
% 6.57/2.45  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.57/2.45  tff(c_248, plain, (![A_49, B_50]: (k5_xboole_0(A_49, k3_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.57/2.45  tff(c_266, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_248])).
% 6.57/2.45  tff(c_235, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_222])).
% 6.57/2.45  tff(c_257, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_235, c_248])).
% 6.57/2.45  tff(c_325, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_257])).
% 6.57/2.45  tff(c_385, plain, (![A_65, B_66]: (k2_xboole_0(A_65, k4_xboole_0(B_66, A_65))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.57/2.45  tff(c_401, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', '#skF_1'))=k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_325, c_385])).
% 6.57/2.45  tff(c_413, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', '#skF_1'))=k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_401])).
% 6.57/2.45  tff(c_3440, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2055, c_413])).
% 6.57/2.45  tff(c_416, plain, (![A_67, C_68, B_69]: (r1_tarski(A_67, C_68) | ~r1_tarski(k2_xboole_0(A_67, B_69), C_68))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.57/2.45  tff(c_437, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, C_71) | ~r1_tarski(k2_xboole_0(B_72, A_70), C_71))), inference(superposition, [status(thm), theory('equality')], [c_2, c_416])).
% 6.57/2.45  tff(c_506, plain, (![A_76, B_77]: (r1_tarski(A_76, k2_xboole_0(B_77, A_76)))), inference(resolution, [status(thm)], [c_64, c_437])).
% 6.57/2.45  tff(c_14, plain, (![A_11, C_13, B_12]: (r1_tarski(A_11, C_13) | ~r1_tarski(k2_xboole_0(A_11, B_12), C_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.57/2.45  tff(c_534, plain, (![A_11, B_77, B_12]: (r1_tarski(A_11, k2_xboole_0(B_77, k2_xboole_0(A_11, B_12))))), inference(resolution, [status(thm)], [c_506, c_14])).
% 6.57/2.45  tff(c_3562, plain, (![B_170]: (r1_tarski('#skF_1', k2_xboole_0(B_170, k4_xboole_0('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_3440, c_534])).
% 6.57/2.45  tff(c_3574, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2754, c_3562])).
% 6.57/2.45  tff(c_3599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150, c_3574])).
% 6.57/2.45  tff(c_3600, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 6.57/2.45  tff(c_12784, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_12776, c_3600])).
% 6.57/2.45  tff(c_12790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_12784])).
% 6.57/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.57/2.45  
% 6.57/2.45  Inference rules
% 6.57/2.45  ----------------------
% 6.57/2.45  #Ref     : 0
% 6.57/2.45  #Sup     : 3075
% 6.57/2.45  #Fact    : 0
% 6.57/2.45  #Define  : 0
% 6.57/2.45  #Split   : 4
% 6.57/2.45  #Chain   : 0
% 6.57/2.45  #Close   : 0
% 6.57/2.45  
% 6.57/2.45  Ordering : KBO
% 6.57/2.45  
% 6.57/2.45  Simplification rules
% 6.57/2.45  ----------------------
% 6.57/2.45  #Subsume      : 120
% 6.57/2.45  #Demod        : 2634
% 6.57/2.45  #Tautology    : 2448
% 6.57/2.45  #SimpNegUnit  : 9
% 6.57/2.45  #BackRed      : 21
% 6.57/2.45  
% 6.57/2.45  #Partial instantiations: 0
% 6.57/2.45  #Strategies tried      : 1
% 6.57/2.45  
% 6.57/2.45  Timing (in seconds)
% 6.57/2.45  ----------------------
% 6.57/2.46  Preprocessing        : 0.32
% 6.57/2.46  Parsing              : 0.18
% 6.57/2.46  CNF conversion       : 0.02
% 6.57/2.46  Main loop            : 1.33
% 6.57/2.46  Inferencing          : 0.43
% 6.57/2.46  Reduction            : 0.57
% 6.57/2.46  Demodulation         : 0.46
% 6.57/2.46  BG Simplification    : 0.04
% 6.57/2.46  Subsumption          : 0.21
% 6.57/2.46  Abstraction          : 0.05
% 6.57/2.46  MUC search           : 0.00
% 6.57/2.46  Cooper               : 0.00
% 6.57/2.46  Total                : 1.69
% 6.57/2.46  Index Insertion      : 0.00
% 6.57/2.46  Index Deletion       : 0.00
% 6.57/2.46  Index Matching       : 0.00
% 6.57/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
