%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:39 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 578 expanded)
%              Number of leaves         :   38 ( 209 expanded)
%              Depth                    :   19
%              Number of atoms          :   84 ( 947 expanded)
%              Number of equality atoms :   58 ( 374 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_85,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_57,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_16,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_58,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_129,plain,(
    ! [A_81,B_82] : r1_tarski(A_81,k2_xboole_0(A_81,B_82)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_132,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_129])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_xboole_0(A_3,B_4)
      | B_4 = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_201,plain,(
    ! [A_98,B_99] :
      ( r2_xboole_0(A_98,B_99)
      | B_99 = A_98
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_xboole_0(B_2,A_1)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_217,plain,(
    ! [B_100,A_101] :
      ( ~ r2_xboole_0(B_100,A_101)
      | B_100 = A_101
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(resolution,[status(thm)],[c_201,c_2])).

tff(c_222,plain,(
    ! [B_102,A_103] :
      ( ~ r1_tarski(B_102,A_103)
      | B_102 = A_103
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(resolution,[status(thm)],[c_4,c_217])).

tff(c_224,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_132,c_222])).

tff(c_233,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_224])).

tff(c_50,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_255,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_50])).

tff(c_258,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_255])).

tff(c_22,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_271,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_22])).

tff(c_221,plain,(
    ! [B_4,A_3] :
      ( ~ r1_tarski(B_4,A_3)
      | B_4 = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_4,c_217])).

tff(c_276,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_271,c_221])).

tff(c_279,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_276])).

tff(c_26,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_171,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_180,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_171])).

tff(c_183,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_180])).

tff(c_52,plain,(
    ! [B_72] : k4_xboole_0(k1_tarski(B_72),k1_tarski(B_72)) != k1_tarski(B_72) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_184,plain,(
    ! [B_72] : k1_tarski(B_72) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_52])).

tff(c_284,plain,(
    ! [B_72] : k1_tarski(B_72) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_184])).

tff(c_20,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_286,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_1') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_20])).

tff(c_288,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_26])).

tff(c_544,plain,(
    ! [A_127,B_128,C_129] : k5_xboole_0(k5_xboole_0(A_127,B_128),C_129) = k5_xboole_0(A_127,k5_xboole_0(B_128,C_129)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_720,plain,(
    ! [A_134,C_135] : k5_xboole_0(A_134,k5_xboole_0(A_134,C_135)) = k5_xboole_0('#skF_1',C_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_544])).

tff(c_782,plain,(
    ! [A_19] : k5_xboole_0(A_19,'#skF_1') = k5_xboole_0('#skF_1',A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_720])).

tff(c_803,plain,(
    ! [A_19] : k5_xboole_0('#skF_1',A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_782])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_287,plain,(
    ! [A_12] : k4_xboole_0('#skF_1',A_12) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_279,c_18])).

tff(c_14,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_596,plain,(
    ! [A_130,B_131] : k5_xboole_0(A_130,k5_xboole_0(B_131,k5_xboole_0(A_130,B_131))) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_288])).

tff(c_642,plain,(
    ! [A_132] : k5_xboole_0(A_132,k5_xboole_0('#skF_1',A_132)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_596])).

tff(c_687,plain,(
    ! [B_10] : k5_xboole_0(k3_xboole_0('#skF_1',B_10),k4_xboole_0('#skF_1',B_10)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_642])).

tff(c_698,plain,(
    ! [B_10] : k3_xboole_0('#skF_1',B_10) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_287,c_687])).

tff(c_281,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_258])).

tff(c_870,plain,(
    ! [A_137,B_138] : k5_xboole_0(k5_xboole_0(A_137,B_138),k2_xboole_0(A_137,B_138)) = k3_xboole_0(A_137,B_138) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_913,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_870])).

tff(c_929,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_803,c_698,c_913])).

tff(c_283,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_233])).

tff(c_937,plain,(
    k2_tarski('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_283])).

tff(c_36,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_950,plain,(
    k1_tarski('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_36])).

tff(c_958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_950])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.37  
% 2.87/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.37  %$ r2_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.87/1.37  
% 2.87/1.37  %Foreground sorts:
% 2.87/1.37  
% 2.87/1.37  
% 2.87/1.37  %Background operators:
% 2.87/1.37  
% 2.87/1.37  
% 2.87/1.37  %Foreground operators:
% 2.87/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.87/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.37  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.87/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.87/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.37  
% 2.87/1.38  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.87/1.38  tff(f_85, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.87/1.38  tff(f_89, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.87/1.38  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.87/1.38  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.87/1.38  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 2.87/1.38  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.87/1.38  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.87/1.38  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.87/1.38  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.87/1.38  tff(f_84, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.87/1.38  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.87/1.38  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.87/1.38  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.87/1.38  tff(f_57, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.87/1.38  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.87/1.38  tff(c_16, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.87/1.38  tff(c_56, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.87/1.38  tff(c_58, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.87/1.38  tff(c_129, plain, (![A_81, B_82]: (r1_tarski(A_81, k2_xboole_0(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.87/1.38  tff(c_132, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_129])).
% 2.87/1.38  tff(c_4, plain, (![A_3, B_4]: (r2_xboole_0(A_3, B_4) | B_4=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.38  tff(c_201, plain, (![A_98, B_99]: (r2_xboole_0(A_98, B_99) | B_99=A_98 | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.38  tff(c_2, plain, (![B_2, A_1]: (~r2_xboole_0(B_2, A_1) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.87/1.38  tff(c_217, plain, (![B_100, A_101]: (~r2_xboole_0(B_100, A_101) | B_100=A_101 | ~r1_tarski(A_101, B_100))), inference(resolution, [status(thm)], [c_201, c_2])).
% 2.87/1.38  tff(c_222, plain, (![B_102, A_103]: (~r1_tarski(B_102, A_103) | B_102=A_103 | ~r1_tarski(A_103, B_102))), inference(resolution, [status(thm)], [c_4, c_217])).
% 2.87/1.38  tff(c_224, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_132, c_222])).
% 2.87/1.38  tff(c_233, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_224])).
% 2.87/1.38  tff(c_50, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.87/1.38  tff(c_255, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_233, c_50])).
% 2.87/1.38  tff(c_258, plain, (k2_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_255])).
% 2.87/1.38  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.87/1.38  tff(c_271, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_258, c_22])).
% 2.87/1.38  tff(c_221, plain, (![B_4, A_3]: (~r1_tarski(B_4, A_3) | B_4=A_3 | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_4, c_217])).
% 2.87/1.38  tff(c_276, plain, (k1_xboole_0='#skF_1' | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_271, c_221])).
% 2.87/1.38  tff(c_279, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_276])).
% 2.87/1.38  tff(c_26, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.87/1.38  tff(c_12, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.87/1.38  tff(c_171, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.38  tff(c_180, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_171])).
% 2.87/1.38  tff(c_183, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_180])).
% 2.87/1.38  tff(c_52, plain, (![B_72]: (k4_xboole_0(k1_tarski(B_72), k1_tarski(B_72))!=k1_tarski(B_72))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.87/1.38  tff(c_184, plain, (![B_72]: (k1_tarski(B_72)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_52])).
% 2.87/1.38  tff(c_284, plain, (![B_72]: (k1_tarski(B_72)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_184])).
% 2.87/1.38  tff(c_20, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.87/1.38  tff(c_286, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_1')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_279, c_20])).
% 2.87/1.38  tff(c_288, plain, (![A_19]: (k5_xboole_0(A_19, A_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_26])).
% 2.87/1.38  tff(c_544, plain, (![A_127, B_128, C_129]: (k5_xboole_0(k5_xboole_0(A_127, B_128), C_129)=k5_xboole_0(A_127, k5_xboole_0(B_128, C_129)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.87/1.38  tff(c_720, plain, (![A_134, C_135]: (k5_xboole_0(A_134, k5_xboole_0(A_134, C_135))=k5_xboole_0('#skF_1', C_135))), inference(superposition, [status(thm), theory('equality')], [c_288, c_544])).
% 2.87/1.38  tff(c_782, plain, (![A_19]: (k5_xboole_0(A_19, '#skF_1')=k5_xboole_0('#skF_1', A_19))), inference(superposition, [status(thm), theory('equality')], [c_288, c_720])).
% 2.87/1.38  tff(c_803, plain, (![A_19]: (k5_xboole_0('#skF_1', A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_782])).
% 2.87/1.38  tff(c_18, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.87/1.38  tff(c_287, plain, (![A_12]: (k4_xboole_0('#skF_1', A_12)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_279, c_18])).
% 2.87/1.38  tff(c_14, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.38  tff(c_596, plain, (![A_130, B_131]: (k5_xboole_0(A_130, k5_xboole_0(B_131, k5_xboole_0(A_130, B_131)))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_544, c_288])).
% 2.87/1.38  tff(c_642, plain, (![A_132]: (k5_xboole_0(A_132, k5_xboole_0('#skF_1', A_132))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_286, c_596])).
% 2.87/1.38  tff(c_687, plain, (![B_10]: (k5_xboole_0(k3_xboole_0('#skF_1', B_10), k4_xboole_0('#skF_1', B_10))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_642])).
% 2.87/1.38  tff(c_698, plain, (![B_10]: (k3_xboole_0('#skF_1', B_10)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_287, c_687])).
% 2.87/1.38  tff(c_281, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_279, c_258])).
% 2.87/1.38  tff(c_870, plain, (![A_137, B_138]: (k5_xboole_0(k5_xboole_0(A_137, B_138), k2_xboole_0(A_137, B_138))=k3_xboole_0(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.87/1.38  tff(c_913, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_281, c_870])).
% 2.87/1.38  tff(c_929, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_803, c_698, c_913])).
% 2.87/1.38  tff(c_283, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_279, c_233])).
% 2.87/1.38  tff(c_937, plain, (k2_tarski('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_929, c_283])).
% 2.87/1.38  tff(c_36, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.87/1.38  tff(c_950, plain, (k1_tarski('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_937, c_36])).
% 2.87/1.38  tff(c_958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_950])).
% 2.87/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.38  
% 2.87/1.38  Inference rules
% 2.87/1.38  ----------------------
% 2.87/1.38  #Ref     : 0
% 2.87/1.38  #Sup     : 219
% 2.87/1.38  #Fact    : 0
% 2.87/1.38  #Define  : 0
% 2.87/1.38  #Split   : 0
% 2.87/1.38  #Chain   : 0
% 2.87/1.38  #Close   : 0
% 2.87/1.38  
% 2.87/1.38  Ordering : KBO
% 2.87/1.38  
% 2.87/1.38  Simplification rules
% 2.87/1.38  ----------------------
% 2.87/1.38  #Subsume      : 2
% 2.87/1.38  #Demod        : 136
% 2.87/1.38  #Tautology    : 162
% 2.87/1.38  #SimpNegUnit  : 3
% 2.87/1.38  #BackRed      : 19
% 2.87/1.38  
% 2.87/1.38  #Partial instantiations: 0
% 2.87/1.38  #Strategies tried      : 1
% 2.87/1.38  
% 2.87/1.38  Timing (in seconds)
% 2.87/1.38  ----------------------
% 2.87/1.39  Preprocessing        : 0.32
% 2.87/1.39  Parsing              : 0.17
% 2.87/1.39  CNF conversion       : 0.02
% 2.87/1.39  Main loop            : 0.30
% 2.87/1.39  Inferencing          : 0.11
% 2.87/1.39  Reduction            : 0.11
% 2.87/1.39  Demodulation         : 0.08
% 2.87/1.39  BG Simplification    : 0.02
% 2.87/1.39  Subsumption          : 0.04
% 2.87/1.39  Abstraction          : 0.02
% 2.87/1.39  MUC search           : 0.00
% 2.87/1.39  Cooper               : 0.00
% 2.87/1.39  Total                : 0.66
% 2.87/1.39  Index Insertion      : 0.00
% 2.87/1.39  Index Deletion       : 0.00
% 2.87/1.39  Index Matching       : 0.00
% 2.87/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
