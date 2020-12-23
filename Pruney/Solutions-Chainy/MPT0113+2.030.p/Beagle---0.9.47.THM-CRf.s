%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:15 EST 2020

% Result     : Theorem 5.95s
% Output     : CNFRefutation 5.95s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 158 expanded)
%              Number of leaves         :   31 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :   80 ( 180 expanded)
%              Number of equality atoms :   47 (  98 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_75,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_12,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,(
    ! [A_45,B_46] : r1_tarski(k3_xboole_0(A_45,B_46),A_45) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_114,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_111])).

tff(c_16,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_52])).

tff(c_36,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76,plain,(
    ! [A_30] : k5_xboole_0(A_30,'#skF_1') = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_36])).

tff(c_40,plain,(
    ! [A_34] : k5_xboole_0(A_34,A_34) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_86,plain,(
    ! [A_34] : k5_xboole_0(A_34,A_34) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_40])).

tff(c_4142,plain,(
    ! [A_166,B_167] : k5_xboole_0(A_166,k3_xboole_0(A_166,B_167)) = k4_xboole_0(A_166,B_167) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4160,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4142])).

tff(c_4193,plain,(
    ! [A_168] : k4_xboole_0(A_168,A_168) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4160])).

tff(c_30,plain,(
    ! [A_22,B_23] : r1_tarski(k4_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4203,plain,(
    ! [A_169] : r1_tarski('#skF_1',A_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_4193,c_30])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4207,plain,(
    ! [A_169] : k3_xboole_0('#skF_1',A_169) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4203,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_13,B_14] : r1_tarski(k3_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4111,plain,(
    ! [A_164,B_165] :
      ( k3_xboole_0(A_164,B_165) = A_164
      | ~ r1_tarski(A_164,B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4814,plain,(
    ! [A_203,B_204] : k3_xboole_0(k3_xboole_0(A_203,B_204),A_203) = k3_xboole_0(A_203,B_204) ),
    inference(resolution,[status(thm)],[c_22,c_4111])).

tff(c_18,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4833,plain,(
    ! [A_203,B_204] : k5_xboole_0(k3_xboole_0(A_203,B_204),k3_xboole_0(A_203,B_204)) = k4_xboole_0(k3_xboole_0(A_203,B_204),A_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_4814,c_18])).

tff(c_4895,plain,(
    ! [A_203,B_204] : k4_xboole_0(k3_xboole_0(A_203,B_204),A_203) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_4833])).

tff(c_5392,plain,(
    ! [A_220,B_221,C_222] : k4_xboole_0(k3_xboole_0(A_220,B_221),C_222) = k3_xboole_0(A_220,k4_xboole_0(B_221,C_222)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5601,plain,(
    ! [A_226,B_227] : k3_xboole_0(A_226,k4_xboole_0(B_227,A_226)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4895,c_5392])).

tff(c_5646,plain,(
    ! [A_226,B_227] : k4_xboole_0(A_226,k4_xboole_0(B_227,A_226)) = k5_xboole_0(A_226,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5601,c_18])).

tff(c_5715,plain,(
    ! [A_228,B_229] : k4_xboole_0(A_228,k4_xboole_0(B_229,A_228)) = A_228 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5646])).

tff(c_5433,plain,(
    ! [A_203,B_204] : k3_xboole_0(A_203,k4_xboole_0(B_204,A_203)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4895,c_5392])).

tff(c_5724,plain,(
    ! [B_229,A_228] : k3_xboole_0(k4_xboole_0(B_229,A_228),A_228) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5715,c_5433])).

tff(c_46,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4141,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_4111])).

tff(c_4908,plain,(
    ! [A_205,B_206,C_207] : k3_xboole_0(k3_xboole_0(A_205,B_206),C_207) = k3_xboole_0(A_205,k3_xboole_0(B_206,C_207)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8416,plain,(
    ! [C_281] : k3_xboole_0('#skF_2',k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),C_281)) = k3_xboole_0('#skF_2',C_281) ),
    inference(superposition,[status(thm),theory(equality)],[c_4141,c_4908])).

tff(c_8505,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5724,c_8416])).

tff(c_8552,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4207,c_2,c_2,c_8505])).

tff(c_8610,plain,(
    k5_xboole_0('#skF_4','#skF_1') = k4_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8552,c_18])).

tff(c_8636,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_8610])).

tff(c_38,plain,(
    ! [A_31,C_33,B_32] :
      ( r1_xboole_0(A_31,k4_xboole_0(C_33,B_32))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9553,plain,(
    ! [A_290] :
      ( r1_xboole_0(A_290,'#skF_4')
      | ~ r1_tarski(A_290,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8636,c_38])).

tff(c_44,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_129,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_170,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_187,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_170])).

tff(c_3804,plain,(
    ! [A_154,B_155] : k3_xboole_0(k4_xboole_0(A_154,B_155),A_154) = k4_xboole_0(A_154,B_155) ),
    inference(resolution,[status(thm)],[c_30,c_170])).

tff(c_1133,plain,(
    ! [A_108,B_109,C_110] : k3_xboole_0(k3_xboole_0(A_108,B_109),C_110) = k3_xboole_0(A_108,k3_xboole_0(B_109,C_110)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1218,plain,(
    ! [C_110] : k3_xboole_0('#skF_2',k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),C_110)) = k3_xboole_0('#skF_2',C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_1133])).

tff(c_3826,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3804,c_1218])).

tff(c_3955,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_2,c_3826])).

tff(c_4035,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3955,c_22])).

tff(c_4050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_4035])).

tff(c_4051,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_9556,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_9553,c_4051])).

tff(c_9560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_9556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.95/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.26  
% 5.95/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.26  %$ r2_xboole_0 > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.95/2.26  
% 5.95/2.26  %Foreground sorts:
% 5.95/2.26  
% 5.95/2.26  
% 5.95/2.26  %Background operators:
% 5.95/2.26  
% 5.95/2.26  
% 5.95/2.26  %Foreground operators:
% 5.95/2.26  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 5.95/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.95/2.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.95/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.95/2.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.95/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.95/2.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.95/2.26  tff('#skF_2', type, '#skF_2': $i).
% 5.95/2.26  tff('#skF_3', type, '#skF_3': $i).
% 5.95/2.26  tff('#skF_1', type, '#skF_1': $i).
% 5.95/2.26  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.95/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.95/2.26  tff('#skF_4', type, '#skF_4': $i).
% 5.95/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.95/2.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.95/2.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.95/2.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.95/2.26  
% 5.95/2.27  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.95/2.27  tff(f_49, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.95/2.27  tff(f_43, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 5.95/2.27  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.95/2.27  tff(f_69, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.95/2.27  tff(f_75, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.95/2.27  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.95/2.27  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.95/2.27  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.95/2.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.95/2.27  tff(f_61, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.95/2.27  tff(f_84, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.95/2.27  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.95/2.27  tff(f_73, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.95/2.27  tff(c_12, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.95/2.27  tff(c_111, plain, (![A_45, B_46]: (r1_tarski(k3_xboole_0(A_45, B_46), A_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.95/2.27  tff(c_114, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_12, c_111])).
% 5.95/2.27  tff(c_16, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.95/2.27  tff(c_52, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.95/2.27  tff(c_56, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_16, c_52])).
% 5.95/2.27  tff(c_36, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=A_30)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.95/2.27  tff(c_76, plain, (![A_30]: (k5_xboole_0(A_30, '#skF_1')=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_36])).
% 5.95/2.27  tff(c_40, plain, (![A_34]: (k5_xboole_0(A_34, A_34)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.95/2.27  tff(c_86, plain, (![A_34]: (k5_xboole_0(A_34, A_34)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_40])).
% 5.95/2.27  tff(c_4142, plain, (![A_166, B_167]: (k5_xboole_0(A_166, k3_xboole_0(A_166, B_167))=k4_xboole_0(A_166, B_167))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.95/2.27  tff(c_4160, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4142])).
% 5.95/2.27  tff(c_4193, plain, (![A_168]: (k4_xboole_0(A_168, A_168)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4160])).
% 5.95/2.27  tff(c_30, plain, (![A_22, B_23]: (r1_tarski(k4_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.95/2.27  tff(c_4203, plain, (![A_169]: (r1_tarski('#skF_1', A_169))), inference(superposition, [status(thm), theory('equality')], [c_4193, c_30])).
% 5.95/2.27  tff(c_28, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.95/2.27  tff(c_4207, plain, (![A_169]: (k3_xboole_0('#skF_1', A_169)='#skF_1')), inference(resolution, [status(thm)], [c_4203, c_28])).
% 5.95/2.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.95/2.27  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(k3_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.95/2.27  tff(c_4111, plain, (![A_164, B_165]: (k3_xboole_0(A_164, B_165)=A_164 | ~r1_tarski(A_164, B_165))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.95/2.27  tff(c_4814, plain, (![A_203, B_204]: (k3_xboole_0(k3_xboole_0(A_203, B_204), A_203)=k3_xboole_0(A_203, B_204))), inference(resolution, [status(thm)], [c_22, c_4111])).
% 5.95/2.27  tff(c_18, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.95/2.27  tff(c_4833, plain, (![A_203, B_204]: (k5_xboole_0(k3_xboole_0(A_203, B_204), k3_xboole_0(A_203, B_204))=k4_xboole_0(k3_xboole_0(A_203, B_204), A_203))), inference(superposition, [status(thm), theory('equality')], [c_4814, c_18])).
% 5.95/2.27  tff(c_4895, plain, (![A_203, B_204]: (k4_xboole_0(k3_xboole_0(A_203, B_204), A_203)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_4833])).
% 5.95/2.27  tff(c_5392, plain, (![A_220, B_221, C_222]: (k4_xboole_0(k3_xboole_0(A_220, B_221), C_222)=k3_xboole_0(A_220, k4_xboole_0(B_221, C_222)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.95/2.27  tff(c_5601, plain, (![A_226, B_227]: (k3_xboole_0(A_226, k4_xboole_0(B_227, A_226))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4895, c_5392])).
% 5.95/2.27  tff(c_5646, plain, (![A_226, B_227]: (k4_xboole_0(A_226, k4_xboole_0(B_227, A_226))=k5_xboole_0(A_226, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5601, c_18])).
% 5.95/2.27  tff(c_5715, plain, (![A_228, B_229]: (k4_xboole_0(A_228, k4_xboole_0(B_229, A_228))=A_228)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5646])).
% 5.95/2.27  tff(c_5433, plain, (![A_203, B_204]: (k3_xboole_0(A_203, k4_xboole_0(B_204, A_203))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4895, c_5392])).
% 5.95/2.27  tff(c_5724, plain, (![B_229, A_228]: (k3_xboole_0(k4_xboole_0(B_229, A_228), A_228)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5715, c_5433])).
% 5.95/2.27  tff(c_46, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.95/2.27  tff(c_4141, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_46, c_4111])).
% 5.95/2.27  tff(c_4908, plain, (![A_205, B_206, C_207]: (k3_xboole_0(k3_xboole_0(A_205, B_206), C_207)=k3_xboole_0(A_205, k3_xboole_0(B_206, C_207)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.95/2.27  tff(c_8416, plain, (![C_281]: (k3_xboole_0('#skF_2', k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), C_281))=k3_xboole_0('#skF_2', C_281))), inference(superposition, [status(thm), theory('equality')], [c_4141, c_4908])).
% 5.95/2.27  tff(c_8505, plain, (k3_xboole_0('#skF_2', '#skF_1')=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5724, c_8416])).
% 5.95/2.27  tff(c_8552, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4207, c_2, c_2, c_8505])).
% 5.95/2.27  tff(c_8610, plain, (k5_xboole_0('#skF_4', '#skF_1')=k4_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8552, c_18])).
% 5.95/2.27  tff(c_8636, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_8610])).
% 5.95/2.27  tff(c_38, plain, (![A_31, C_33, B_32]: (r1_xboole_0(A_31, k4_xboole_0(C_33, B_32)) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.95/2.27  tff(c_9553, plain, (![A_290]: (r1_xboole_0(A_290, '#skF_4') | ~r1_tarski(A_290, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8636, c_38])).
% 5.95/2.27  tff(c_44, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.95/2.27  tff(c_129, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 5.95/2.27  tff(c_170, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.95/2.27  tff(c_187, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_46, c_170])).
% 5.95/2.27  tff(c_3804, plain, (![A_154, B_155]: (k3_xboole_0(k4_xboole_0(A_154, B_155), A_154)=k4_xboole_0(A_154, B_155))), inference(resolution, [status(thm)], [c_30, c_170])).
% 5.95/2.27  tff(c_1133, plain, (![A_108, B_109, C_110]: (k3_xboole_0(k3_xboole_0(A_108, B_109), C_110)=k3_xboole_0(A_108, k3_xboole_0(B_109, C_110)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.95/2.27  tff(c_1218, plain, (![C_110]: (k3_xboole_0('#skF_2', k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), C_110))=k3_xboole_0('#skF_2', C_110))), inference(superposition, [status(thm), theory('equality')], [c_187, c_1133])).
% 5.95/2.27  tff(c_3826, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3804, c_1218])).
% 5.95/2.27  tff(c_3955, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_187, c_2, c_3826])).
% 5.95/2.27  tff(c_4035, plain, (r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3955, c_22])).
% 5.95/2.27  tff(c_4050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_4035])).
% 5.95/2.27  tff(c_4051, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 5.95/2.27  tff(c_9556, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_9553, c_4051])).
% 5.95/2.27  tff(c_9560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_9556])).
% 5.95/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.27  
% 5.95/2.27  Inference rules
% 5.95/2.27  ----------------------
% 5.95/2.27  #Ref     : 0
% 5.95/2.27  #Sup     : 2419
% 5.95/2.27  #Fact    : 0
% 5.95/2.27  #Define  : 0
% 5.95/2.27  #Split   : 1
% 5.95/2.27  #Chain   : 0
% 5.95/2.27  #Close   : 0
% 5.95/2.27  
% 5.95/2.27  Ordering : KBO
% 5.95/2.27  
% 5.95/2.27  Simplification rules
% 5.95/2.27  ----------------------
% 5.95/2.27  #Subsume      : 45
% 5.95/2.27  #Demod        : 2003
% 5.95/2.27  #Tautology    : 1734
% 5.95/2.27  #SimpNegUnit  : 1
% 5.95/2.27  #BackRed      : 2
% 5.95/2.27  
% 5.95/2.27  #Partial instantiations: 0
% 5.95/2.27  #Strategies tried      : 1
% 5.95/2.27  
% 5.95/2.27  Timing (in seconds)
% 5.95/2.27  ----------------------
% 5.95/2.28  Preprocessing        : 0.31
% 5.95/2.28  Parsing              : 0.16
% 5.95/2.28  CNF conversion       : 0.02
% 5.95/2.28  Main loop            : 1.21
% 5.95/2.28  Inferencing          : 0.37
% 5.95/2.28  Reduction            : 0.55
% 5.95/2.28  Demodulation         : 0.45
% 5.95/2.28  BG Simplification    : 0.04
% 5.95/2.28  Subsumption          : 0.17
% 5.95/2.28  Abstraction          : 0.05
% 5.95/2.28  MUC search           : 0.00
% 5.95/2.28  Cooper               : 0.00
% 5.95/2.28  Total                : 1.56
% 5.95/2.28  Index Insertion      : 0.00
% 5.95/2.28  Index Deletion       : 0.00
% 5.95/2.28  Index Matching       : 0.00
% 5.95/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
