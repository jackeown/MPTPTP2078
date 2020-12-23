%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:51 EST 2020

% Result     : Theorem 11.57s
% Output     : CNFRefutation 11.69s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 200 expanded)
%              Number of leaves         :   25 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  103 ( 226 expanded)
%              Number of equality atoms :   67 ( 147 expanded)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_87,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [A_37] : k2_xboole_0(k1_xboole_0,A_37) = A_37 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_365,plain,(
    ! [A_49,B_50] :
      ( k2_xboole_0(A_49,B_50) = B_50
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_513,plain,(
    ! [A_54,B_55] : k2_xboole_0(k4_xboole_0(A_54,B_55),A_54) = A_54 ),
    inference(resolution,[status(thm)],[c_14,c_365])).

tff(c_532,plain,(
    ! [B_55] : k4_xboole_0(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_10])).

tff(c_774,plain,(
    ! [A_64,B_65] : k4_xboole_0(k2_xboole_0(A_64,B_65),B_65) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_818,plain,(
    ! [A_37] : k4_xboole_0(k1_xboole_0,A_37) = k4_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_774])).

tff(c_834,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_818])).

tff(c_1088,plain,(
    ! [A_73,B_74,C_75] : k4_xboole_0(k4_xboole_0(A_73,B_74),C_75) = k4_xboole_0(A_73,k2_xboole_0(B_74,C_75)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1127,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k2_xboole_0(B_74,k4_xboole_0(A_73,B_74))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_1088])).

tff(c_1148,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k2_xboole_0(B_74,A_73)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1127])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k4_xboole_0(A_18,B_19),C_20) = k4_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_396,plain,(
    ! [A_7,B_8] : k2_xboole_0(k3_xboole_0(A_7,B_8),A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_8,c_365])).

tff(c_539,plain,(
    ! [B_2,B_55] : k2_xboole_0(B_2,k4_xboole_0(B_2,B_55)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_513])).

tff(c_394,plain,(
    ! [A_12,B_13] : k2_xboole_0(k4_xboole_0(A_12,B_13),A_12) = A_12 ),
    inference(resolution,[status(thm)],[c_14,c_365])).

tff(c_18,plain,(
    ! [A_16,B_17] : k4_xboole_0(k2_xboole_0(A_16,B_17),B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1130,plain,(
    ! [A_16,B_17,C_75] : k4_xboole_0(k2_xboole_0(A_16,B_17),k2_xboole_0(B_17,C_75)) = k4_xboole_0(k4_xboole_0(A_16,B_17),C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1088])).

tff(c_4911,plain,(
    ! [A_136,B_137,C_138] : k4_xboole_0(k2_xboole_0(A_136,B_137),k2_xboole_0(B_137,C_138)) = k4_xboole_0(A_136,k2_xboole_0(B_137,C_138)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1130])).

tff(c_5065,plain,(
    ! [A_136,A_12,B_13] : k4_xboole_0(k2_xboole_0(A_136,k4_xboole_0(A_12,B_13)),A_12) = k4_xboole_0(A_136,k2_xboole_0(k4_xboole_0(A_12,B_13),A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_4911])).

tff(c_16758,plain,(
    ! [A_239,A_240,B_241] : k4_xboole_0(k2_xboole_0(A_239,k4_xboole_0(A_240,B_241)),A_240) = k4_xboole_0(A_239,A_240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_2,c_5065])).

tff(c_17052,plain,(
    ! [A_240,B_241,B_8] : k4_xboole_0(k3_xboole_0(k4_xboole_0(A_240,B_241),B_8),A_240) = k4_xboole_0(k4_xboole_0(A_240,B_241),A_240) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_16758])).

tff(c_17570,plain,(
    ! [A_245,B_246,B_247] : k4_xboole_0(k3_xboole_0(k4_xboole_0(A_245,B_246),B_247),A_245) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_20,c_17052])).

tff(c_17709,plain,(
    ! [A_245,B_246,B_247] : k2_xboole_0(A_245,k3_xboole_0(k4_xboole_0(A_245,B_246),B_247)) = k2_xboole_0(A_245,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_17570,c_16])).

tff(c_18034,plain,(
    ! [A_248,B_249,B_250] : k2_xboole_0(A_248,k3_xboole_0(k4_xboole_0(A_248,B_249),B_250)) = A_248 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_17709])).

tff(c_24,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_105,plain,(
    ! [B_36,A_37] : r1_tarski(B_36,k2_xboole_0(A_37,B_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_24])).

tff(c_18485,plain,(
    ! [A_251,B_252,B_253] : r1_tarski(k3_xboole_0(k4_xboole_0(A_251,B_252),B_253),A_251) ),
    inference(superposition,[status(thm),theory(equality)],[c_18034,c_105])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1186,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_xboole_0 = A_76
      | ~ r1_xboole_0(B_77,C_78)
      | ~ r1_tarski(A_76,C_78)
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1269,plain,(
    ! [A_81] :
      ( k1_xboole_0 = A_81
      | ~ r1_tarski(A_81,'#skF_3')
      | ~ r1_tarski(A_81,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_1186])).

tff(c_2257,plain,(
    ! [B_102] :
      ( k3_xboole_0('#skF_3',B_102) = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0('#skF_3',B_102),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_1269])).

tff(c_2281,plain,(
    ! [B_4] :
      ( k3_xboole_0('#skF_3',B_4) = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0(B_4,'#skF_3'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2257])).

tff(c_18688,plain,(
    ! [B_252] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_1',B_252)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18485,c_2281])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_31,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_395,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_31,c_365])).

tff(c_812,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_2'),k2_xboole_0('#skF_3','#skF_2')) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_774])).

tff(c_1156,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_812])).

tff(c_4251,plain,(
    ! [C_130,A_131,B_132] : k2_xboole_0(C_130,k4_xboole_0(A_131,k2_xboole_0(B_132,C_130))) = k2_xboole_0(C_130,k4_xboole_0(A_131,B_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_16])).

tff(c_37128,plain,(
    ! [A_367,A_368,B_369] : k2_xboole_0(A_367,k4_xboole_0(A_368,k2_xboole_0(A_367,B_369))) = k2_xboole_0(A_367,k4_xboole_0(A_368,B_369)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4251])).

tff(c_37590,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_37128])).

tff(c_37774,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_37590])).

tff(c_41,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_41])).

tff(c_184,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_207,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(resolution,[status(thm)],[c_44,c_184])).

tff(c_315,plain,(
    ! [B_45,A_46] : r1_tarski(B_45,k2_xboole_0(A_46,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_24])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_331,plain,(
    ! [B_45,A_46] : k3_xboole_0(B_45,k2_xboole_0(A_46,B_45)) = B_45 ),
    inference(resolution,[status(thm)],[c_315,c_12])).

tff(c_48,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_336,plain,(
    ! [A_47,B_48] : r1_tarski(k3_xboole_0(A_47,B_48),B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_8])).

tff(c_3199,plain,(
    ! [A_115,B_116] : k3_xboole_0(k3_xboole_0(A_115,B_116),B_116) = k3_xboole_0(A_115,B_116) ),
    inference(resolution,[status(thm)],[c_336,c_12])).

tff(c_8085,plain,(
    ! [A_170,B_171] : k3_xboole_0(k3_xboole_0(A_170,B_171),A_170) = k3_xboole_0(B_171,A_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3199])).

tff(c_8228,plain,(
    ! [A_46,B_45] : k3_xboole_0(k2_xboole_0(A_46,B_45),B_45) = k3_xboole_0(B_45,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_8085])).

tff(c_8298,plain,(
    ! [A_46,B_45] : k3_xboole_0(k2_xboole_0(A_46,B_45),B_45) = B_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_8228])).

tff(c_37879,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_37774,c_8298])).

tff(c_37988,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18688,c_37879])).

tff(c_398,plain,(
    ! [A_24,B_25] : k2_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(resolution,[status(thm)],[c_24,c_365])).

tff(c_3037,plain,(
    ! [B_113,A_114] : k2_xboole_0(B_113,k2_xboole_0(A_114,B_113)) = k2_xboole_0(A_114,B_113) ),
    inference(resolution,[status(thm)],[c_105,c_365])).

tff(c_7115,plain,(
    ! [B_162,A_163] : k2_xboole_0(B_162,k2_xboole_0(B_162,A_163)) = k2_xboole_0(A_163,B_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3037])).

tff(c_7283,plain,(
    ! [B_15,A_14] : k2_xboole_0(k4_xboole_0(B_15,A_14),A_14) = k2_xboole_0(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_7115])).

tff(c_7350,plain,(
    ! [B_15,A_14] : k2_xboole_0(k4_xboole_0(B_15,A_14),A_14) = k2_xboole_0(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_7283])).

tff(c_38086,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_2') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37988,c_7350])).

tff(c_38164,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2,c_38086])).

tff(c_38528,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38164,c_24])).

tff(c_38573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_38528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.57/5.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.65/5.44  
% 11.65/5.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.65/5.44  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.65/5.44  
% 11.65/5.44  %Foreground sorts:
% 11.65/5.44  
% 11.65/5.44  
% 11.65/5.44  %Background operators:
% 11.65/5.44  
% 11.65/5.44  
% 11.65/5.44  %Foreground operators:
% 11.65/5.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.65/5.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.65/5.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.65/5.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.65/5.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.65/5.44  tff('#skF_2', type, '#skF_2': $i).
% 11.65/5.44  tff('#skF_3', type, '#skF_3': $i).
% 11.65/5.44  tff('#skF_1', type, '#skF_1': $i).
% 11.65/5.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.65/5.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.65/5.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.65/5.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.65/5.44  
% 11.69/5.46  tff(f_66, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 11.69/5.46  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.69/5.46  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 11.69/5.46  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.69/5.46  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.69/5.46  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.69/5.46  tff(f_47, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 11.69/5.46  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.69/5.46  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.69/5.46  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.69/5.46  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.69/5.46  tff(f_57, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 11.69/5.46  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.69/5.46  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.69/5.46  tff(c_87, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.69/5.46  tff(c_10, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.69/5.46  tff(c_109, plain, (![A_37]: (k2_xboole_0(k1_xboole_0, A_37)=A_37)), inference(superposition, [status(thm), theory('equality')], [c_87, c_10])).
% 11.69/5.46  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.69/5.46  tff(c_16, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.69/5.46  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.69/5.46  tff(c_365, plain, (![A_49, B_50]: (k2_xboole_0(A_49, B_50)=B_50 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.69/5.46  tff(c_513, plain, (![A_54, B_55]: (k2_xboole_0(k4_xboole_0(A_54, B_55), A_54)=A_54)), inference(resolution, [status(thm)], [c_14, c_365])).
% 11.69/5.46  tff(c_532, plain, (![B_55]: (k4_xboole_0(k1_xboole_0, B_55)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_513, c_10])).
% 11.69/5.46  tff(c_774, plain, (![A_64, B_65]: (k4_xboole_0(k2_xboole_0(A_64, B_65), B_65)=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.69/5.46  tff(c_818, plain, (![A_37]: (k4_xboole_0(k1_xboole_0, A_37)=k4_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_109, c_774])).
% 11.69/5.46  tff(c_834, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_532, c_818])).
% 11.69/5.46  tff(c_1088, plain, (![A_73, B_74, C_75]: (k4_xboole_0(k4_xboole_0(A_73, B_74), C_75)=k4_xboole_0(A_73, k2_xboole_0(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.69/5.46  tff(c_1127, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k2_xboole_0(B_74, k4_xboole_0(A_73, B_74)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_834, c_1088])).
% 11.69/5.46  tff(c_1148, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k2_xboole_0(B_74, A_73))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1127])).
% 11.69/5.46  tff(c_20, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k4_xboole_0(A_18, B_19), C_20)=k4_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.69/5.46  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.69/5.46  tff(c_396, plain, (![A_7, B_8]: (k2_xboole_0(k3_xboole_0(A_7, B_8), A_7)=A_7)), inference(resolution, [status(thm)], [c_8, c_365])).
% 11.69/5.46  tff(c_539, plain, (![B_2, B_55]: (k2_xboole_0(B_2, k4_xboole_0(B_2, B_55))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_513])).
% 11.69/5.46  tff(c_394, plain, (![A_12, B_13]: (k2_xboole_0(k4_xboole_0(A_12, B_13), A_12)=A_12)), inference(resolution, [status(thm)], [c_14, c_365])).
% 11.69/5.46  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(k2_xboole_0(A_16, B_17), B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.69/5.46  tff(c_1130, plain, (![A_16, B_17, C_75]: (k4_xboole_0(k2_xboole_0(A_16, B_17), k2_xboole_0(B_17, C_75))=k4_xboole_0(k4_xboole_0(A_16, B_17), C_75))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1088])).
% 11.69/5.46  tff(c_4911, plain, (![A_136, B_137, C_138]: (k4_xboole_0(k2_xboole_0(A_136, B_137), k2_xboole_0(B_137, C_138))=k4_xboole_0(A_136, k2_xboole_0(B_137, C_138)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1130])).
% 11.69/5.46  tff(c_5065, plain, (![A_136, A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_136, k4_xboole_0(A_12, B_13)), A_12)=k4_xboole_0(A_136, k2_xboole_0(k4_xboole_0(A_12, B_13), A_12)))), inference(superposition, [status(thm), theory('equality')], [c_394, c_4911])).
% 11.69/5.46  tff(c_16758, plain, (![A_239, A_240, B_241]: (k4_xboole_0(k2_xboole_0(A_239, k4_xboole_0(A_240, B_241)), A_240)=k4_xboole_0(A_239, A_240))), inference(demodulation, [status(thm), theory('equality')], [c_539, c_2, c_5065])).
% 11.69/5.46  tff(c_17052, plain, (![A_240, B_241, B_8]: (k4_xboole_0(k3_xboole_0(k4_xboole_0(A_240, B_241), B_8), A_240)=k4_xboole_0(k4_xboole_0(A_240, B_241), A_240))), inference(superposition, [status(thm), theory('equality')], [c_396, c_16758])).
% 11.69/5.46  tff(c_17570, plain, (![A_245, B_246, B_247]: (k4_xboole_0(k3_xboole_0(k4_xboole_0(A_245, B_246), B_247), A_245)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_20, c_17052])).
% 11.69/5.46  tff(c_17709, plain, (![A_245, B_246, B_247]: (k2_xboole_0(A_245, k3_xboole_0(k4_xboole_0(A_245, B_246), B_247))=k2_xboole_0(A_245, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_17570, c_16])).
% 11.69/5.46  tff(c_18034, plain, (![A_248, B_249, B_250]: (k2_xboole_0(A_248, k3_xboole_0(k4_xboole_0(A_248, B_249), B_250))=A_248)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_17709])).
% 11.69/5.46  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.69/5.46  tff(c_105, plain, (![B_36, A_37]: (r1_tarski(B_36, k2_xboole_0(A_37, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_24])).
% 11.69/5.46  tff(c_18485, plain, (![A_251, B_252, B_253]: (r1_tarski(k3_xboole_0(k4_xboole_0(A_251, B_252), B_253), A_251))), inference(superposition, [status(thm), theory('equality')], [c_18034, c_105])).
% 11.69/5.46  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.69/5.46  tff(c_28, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.69/5.46  tff(c_1186, plain, (![A_76, B_77, C_78]: (k1_xboole_0=A_76 | ~r1_xboole_0(B_77, C_78) | ~r1_tarski(A_76, C_78) | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.69/5.46  tff(c_1269, plain, (![A_81]: (k1_xboole_0=A_81 | ~r1_tarski(A_81, '#skF_3') | ~r1_tarski(A_81, '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_1186])).
% 11.69/5.46  tff(c_2257, plain, (![B_102]: (k3_xboole_0('#skF_3', B_102)=k1_xboole_0 | ~r1_tarski(k3_xboole_0('#skF_3', B_102), '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_1269])).
% 11.69/5.46  tff(c_2281, plain, (![B_4]: (k3_xboole_0('#skF_3', B_4)=k1_xboole_0 | ~r1_tarski(k3_xboole_0(B_4, '#skF_3'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2257])).
% 11.69/5.46  tff(c_18688, plain, (![B_252]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_1', B_252))=k1_xboole_0)), inference(resolution, [status(thm)], [c_18485, c_2281])).
% 11.69/5.46  tff(c_30, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.69/5.46  tff(c_31, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 11.69/5.46  tff(c_395, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_31, c_365])).
% 11.69/5.46  tff(c_812, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_2'), k2_xboole_0('#skF_3', '#skF_2'))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_395, c_774])).
% 11.69/5.46  tff(c_1156, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_834, c_812])).
% 11.69/5.46  tff(c_4251, plain, (![C_130, A_131, B_132]: (k2_xboole_0(C_130, k4_xboole_0(A_131, k2_xboole_0(B_132, C_130)))=k2_xboole_0(C_130, k4_xboole_0(A_131, B_132)))), inference(superposition, [status(thm), theory('equality')], [c_1088, c_16])).
% 11.69/5.46  tff(c_37128, plain, (![A_367, A_368, B_369]: (k2_xboole_0(A_367, k4_xboole_0(A_368, k2_xboole_0(A_367, B_369)))=k2_xboole_0(A_367, k4_xboole_0(A_368, B_369)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4251])).
% 11.69/5.46  tff(c_37590, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1156, c_37128])).
% 11.69/5.46  tff(c_37774, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_37590])).
% 11.69/5.46  tff(c_41, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.69/5.46  tff(c_44, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_41])).
% 11.69/5.46  tff(c_184, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.69/5.46  tff(c_207, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(resolution, [status(thm)], [c_44, c_184])).
% 11.69/5.46  tff(c_315, plain, (![B_45, A_46]: (r1_tarski(B_45, k2_xboole_0(A_46, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_24])).
% 11.69/5.46  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.69/5.46  tff(c_331, plain, (![B_45, A_46]: (k3_xboole_0(B_45, k2_xboole_0(A_46, B_45))=B_45)), inference(resolution, [status(thm)], [c_315, c_12])).
% 11.69/5.46  tff(c_48, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.69/5.46  tff(c_336, plain, (![A_47, B_48]: (r1_tarski(k3_xboole_0(A_47, B_48), B_48))), inference(superposition, [status(thm), theory('equality')], [c_48, c_8])).
% 11.69/5.46  tff(c_3199, plain, (![A_115, B_116]: (k3_xboole_0(k3_xboole_0(A_115, B_116), B_116)=k3_xboole_0(A_115, B_116))), inference(resolution, [status(thm)], [c_336, c_12])).
% 11.69/5.46  tff(c_8085, plain, (![A_170, B_171]: (k3_xboole_0(k3_xboole_0(A_170, B_171), A_170)=k3_xboole_0(B_171, A_170))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3199])).
% 11.69/5.46  tff(c_8228, plain, (![A_46, B_45]: (k3_xboole_0(k2_xboole_0(A_46, B_45), B_45)=k3_xboole_0(B_45, B_45))), inference(superposition, [status(thm), theory('equality')], [c_331, c_8085])).
% 11.69/5.46  tff(c_8298, plain, (![A_46, B_45]: (k3_xboole_0(k2_xboole_0(A_46, B_45), B_45)=B_45)), inference(demodulation, [status(thm), theory('equality')], [c_207, c_8228])).
% 11.69/5.46  tff(c_37879, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_37774, c_8298])).
% 11.69/5.46  tff(c_37988, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18688, c_37879])).
% 11.69/5.46  tff(c_398, plain, (![A_24, B_25]: (k2_xboole_0(A_24, k2_xboole_0(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(resolution, [status(thm)], [c_24, c_365])).
% 11.69/5.46  tff(c_3037, plain, (![B_113, A_114]: (k2_xboole_0(B_113, k2_xboole_0(A_114, B_113))=k2_xboole_0(A_114, B_113))), inference(resolution, [status(thm)], [c_105, c_365])).
% 11.69/5.46  tff(c_7115, plain, (![B_162, A_163]: (k2_xboole_0(B_162, k2_xboole_0(B_162, A_163))=k2_xboole_0(A_163, B_162))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3037])).
% 11.69/5.46  tff(c_7283, plain, (![B_15, A_14]: (k2_xboole_0(k4_xboole_0(B_15, A_14), A_14)=k2_xboole_0(A_14, k2_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_7115])).
% 11.69/5.46  tff(c_7350, plain, (![B_15, A_14]: (k2_xboole_0(k4_xboole_0(B_15, A_14), A_14)=k2_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_398, c_7283])).
% 11.69/5.46  tff(c_38086, plain, (k2_xboole_0(k1_xboole_0, '#skF_2')=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37988, c_7350])).
% 11.69/5.46  tff(c_38164, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_2, c_38086])).
% 11.69/5.46  tff(c_38528, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_38164, c_24])).
% 11.69/5.46  tff(c_38573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_38528])).
% 11.69/5.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.69/5.46  
% 11.69/5.46  Inference rules
% 11.69/5.46  ----------------------
% 11.69/5.46  #Ref     : 0
% 11.69/5.46  #Sup     : 9451
% 11.69/5.46  #Fact    : 0
% 11.69/5.46  #Define  : 0
% 11.69/5.46  #Split   : 1
% 11.69/5.46  #Chain   : 0
% 11.69/5.46  #Close   : 0
% 11.69/5.46  
% 11.69/5.46  Ordering : KBO
% 11.69/5.46  
% 11.69/5.46  Simplification rules
% 11.69/5.46  ----------------------
% 11.69/5.46  #Subsume      : 218
% 11.69/5.46  #Demod        : 11695
% 11.69/5.46  #Tautology    : 7116
% 11.69/5.46  #SimpNegUnit  : 1
% 11.69/5.46  #BackRed      : 1
% 11.69/5.46  
% 11.69/5.46  #Partial instantiations: 0
% 11.69/5.46  #Strategies tried      : 1
% 11.69/5.46  
% 11.69/5.46  Timing (in seconds)
% 11.69/5.46  ----------------------
% 11.69/5.46  Preprocessing        : 0.28
% 11.69/5.46  Parsing              : 0.15
% 11.69/5.46  CNF conversion       : 0.02
% 11.69/5.46  Main loop            : 4.40
% 11.69/5.46  Inferencing          : 0.73
% 11.69/5.46  Reduction            : 2.75
% 11.69/5.46  Demodulation         : 2.50
% 11.69/5.46  BG Simplification    : 0.08
% 11.69/5.46  Subsumption          : 0.66
% 11.69/5.46  Abstraction          : 0.15
% 11.69/5.46  MUC search           : 0.00
% 11.69/5.46  Cooper               : 0.00
% 11.69/5.46  Total                : 4.72
% 11.69/5.46  Index Insertion      : 0.00
% 11.69/5.46  Index Deletion       : 0.00
% 11.69/5.46  Index Matching       : 0.00
% 11.69/5.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
