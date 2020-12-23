%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:21 EST 2020

% Result     : Theorem 10.44s
% Output     : CNFRefutation 10.61s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 381 expanded)
%              Number of leaves         :   28 ( 142 expanded)
%              Depth                    :   19
%              Number of atoms          :  105 ( 421 expanded)
%              Number of equality atoms :   75 ( 324 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_246,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k4_xboole_0(A_54,B_55)) = k3_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_276,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_246])).

tff(c_284,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_276])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_289,plain,(
    ! [A_56] : k4_xboole_0(A_56,k1_xboole_0) = k3_xboole_0(A_56,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_20])).

tff(c_313,plain,(
    ! [A_56] : k3_xboole_0(A_56,A_56) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_289])).

tff(c_65,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_81,plain,(
    ! [A_39] : k2_xboole_0(k1_xboole_0,A_39) = A_39 ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_10])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] : k4_xboole_0(k3_xboole_0(A_19,B_20),C_21) = k3_xboole_0(A_19,k4_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_176,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_30,B_31] : r1_xboole_0(k4_xboole_0(A_30,B_31),B_31) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_185,plain,(
    ! [A_44,B_45] : r1_xboole_0(k4_xboole_0(A_44,B_45),k3_xboole_0(A_44,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_30])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_228,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,k3_xboole_0(A_50,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_406,plain,(
    ! [A_64,B_65] :
      ( ~ r1_xboole_0(A_64,B_65)
      | k3_xboole_0(A_64,B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_228])).

tff(c_423,plain,(
    ! [A_44,B_45] : k3_xboole_0(k4_xboole_0(A_44,B_45),k3_xboole_0(A_44,B_45)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_185,c_406])).

tff(c_647,plain,(
    ! [A_70,B_71,C_72] : k4_xboole_0(k3_xboole_0(A_70,B_71),C_72) = k3_xboole_0(A_70,k4_xboole_0(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_707,plain,(
    ! [A_70,B_71,B_18] : k3_xboole_0(A_70,k4_xboole_0(B_71,k4_xboole_0(k3_xboole_0(A_70,B_71),B_18))) = k3_xboole_0(k3_xboole_0(A_70,B_71),B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_647])).

tff(c_17375,plain,(
    ! [A_258,B_259,B_260] : k3_xboole_0(A_258,k4_xboole_0(B_259,k3_xboole_0(A_258,k4_xboole_0(B_259,B_260)))) = k3_xboole_0(k3_xboole_0(A_258,B_259),B_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_707])).

tff(c_17818,plain,(
    ! [B_259,B_260] : k3_xboole_0(k4_xboole_0(B_259,B_260),k4_xboole_0(B_259,k4_xboole_0(B_259,B_260))) = k3_xboole_0(k3_xboole_0(k4_xboole_0(B_259,B_260),B_259),B_260) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_17375])).

tff(c_18308,plain,(
    ! [B_263,B_264] : k3_xboole_0(k3_xboole_0(k4_xboole_0(B_263,B_264),B_263),B_264) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_20,c_17818])).

tff(c_26,plain,(
    ! [A_25,B_26] : k2_xboole_0(k3_xboole_0(A_25,B_26),k4_xboole_0(A_25,B_26)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18510,plain,(
    ! [B_263,B_264] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(k4_xboole_0(B_263,B_264),B_263),B_264)) = k3_xboole_0(k4_xboole_0(B_263,B_264),B_263) ),
    inference(superposition,[status(thm),theory(equality)],[c_18308,c_26])).

tff(c_18700,plain,(
    ! [B_263,B_264] : k3_xboole_0(k4_xboole_0(B_263,B_264),B_263) = k4_xboole_0(B_263,B_264) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_81,c_22,c_18510])).

tff(c_1617,plain,(
    ! [A_99,B_100,C_101] : k4_xboole_0(k3_xboole_0(A_99,B_100),k3_xboole_0(A_99,C_101)) = k3_xboole_0(A_99,k4_xboole_0(B_100,C_101)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1649,plain,(
    ! [A_99,B_100,C_101] : k3_xboole_0(A_99,k4_xboole_0(B_100,k3_xboole_0(A_99,C_101))) = k3_xboole_0(A_99,k4_xboole_0(B_100,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1617,c_22])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_273,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,k3_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_246])).

tff(c_282,plain,(
    ! [A_15,B_16] : k3_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_273])).

tff(c_14861,plain,(
    ! [A_245,B_246,C_247] : k4_xboole_0(k3_xboole_0(A_245,B_246),k3_xboole_0(A_245,k4_xboole_0(B_246,C_247))) = k3_xboole_0(k3_xboole_0(A_245,B_246),C_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_20])).

tff(c_15215,plain,(
    ! [A_15,B_16,C_247] : k4_xboole_0(k3_xboole_0(A_15,B_16),k3_xboole_0(A_15,k4_xboole_0(k3_xboole_0(A_15,B_16),C_247))) = k3_xboole_0(k3_xboole_0(A_15,k3_xboole_0(A_15,B_16)),C_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_14861])).

tff(c_15364,plain,(
    ! [A_15,B_16,C_247] : k3_xboole_0(k3_xboole_0(A_15,B_16),C_247) = k3_xboole_0(A_15,k3_xboole_0(B_16,C_247)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1649,c_282,c_282,c_22,c_22,c_15215])).

tff(c_35070,plain,(
    ! [A_364,B_365,C_366] : k3_xboole_0(k3_xboole_0(A_364,B_365),C_366) = k3_xboole_0(A_364,k3_xboole_0(B_365,C_366)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1649,c_282,c_282,c_22,c_22,c_15215])).

tff(c_267,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_246])).

tff(c_280,plain,(
    ! [A_17,B_18] : k3_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_267])).

tff(c_301,plain,(
    ! [A_56] : r1_xboole_0(k1_xboole_0,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_30])).

tff(c_453,plain,(
    ! [A_66] : k3_xboole_0(k1_xboole_0,A_66) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_301,c_406])).

tff(c_474,plain,(
    ! [A_66] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_18])).

tff(c_494,plain,(
    ! [A_66] : k4_xboole_0(k1_xboole_0,A_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_474])).

tff(c_1159,plain,(
    ! [A_87,B_88,C_89] : k2_xboole_0(k4_xboole_0(A_87,B_88),k3_xboole_0(A_87,C_89)) = k4_xboole_0(A_87,k4_xboole_0(B_88,C_89)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1222,plain,(
    ! [A_14,C_89] : k4_xboole_0(A_14,k4_xboole_0(k1_xboole_0,C_89)) = k2_xboole_0(A_14,k3_xboole_0(A_14,C_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1159])).

tff(c_1237,plain,(
    ! [A_90,C_91] : k2_xboole_0(A_90,k3_xboole_0(A_90,C_91)) = A_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_494,c_1222])).

tff(c_1256,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_1237])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6389,plain,(
    ! [A_159,C_160,B_161] : k2_xboole_0(k3_xboole_0(A_159,C_160),k4_xboole_0(A_159,B_161)) = k4_xboole_0(A_159,k4_xboole_0(B_161,C_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1159])).

tff(c_6514,plain,(
    ! [A_56,B_161] : k4_xboole_0(A_56,k4_xboole_0(B_161,A_56)) = k2_xboole_0(A_56,k4_xboole_0(A_56,B_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_6389])).

tff(c_6725,plain,(
    ! [A_164,B_165] : k4_xboole_0(A_164,k4_xboole_0(B_165,A_164)) = A_164 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1256,c_6514])).

tff(c_426,plain,(
    ! [A_30,B_31] : k3_xboole_0(k4_xboole_0(A_30,B_31),B_31) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_406])).

tff(c_6839,plain,(
    ! [A_164,B_165] : k3_xboole_0(A_164,k4_xboole_0(B_165,A_164)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6725,c_426])).

tff(c_34,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_427,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_406])).

tff(c_13264,plain,(
    ! [A_236,B_237,C_238] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_236,B_237),C_238),k3_xboole_0(A_236,k4_xboole_0(B_237,C_238))) = k3_xboole_0(A_236,B_237) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_26])).

tff(c_13537,plain,(
    k2_xboole_0(k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),'#skF_5'),k1_xboole_0) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_13264])).

tff(c_14464,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),'#skF_5') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13537,c_10])).

tff(c_14533,plain,(
    ! [B_100] : k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k4_xboole_0(B_100,k3_xboole_0('#skF_3','#skF_4'))) = k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k4_xboole_0(B_100,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14464,c_1649])).

tff(c_14602,plain,(
    ! [B_100] : k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k4_xboole_0(B_100,'#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6839,c_14533])).

tff(c_35842,plain,(
    ! [B_368] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',k4_xboole_0(B_368,'#skF_5'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35070,c_14602])).

tff(c_283,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_276])).

tff(c_1000,plain,(
    ! [A_83,B_84] : k3_xboole_0(A_83,k4_xboole_0(B_84,k3_xboole_0(A_83,B_84))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_647])).

tff(c_1039,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k4_xboole_0(B_84,k3_xboole_0(A_83,B_84))) = k4_xboole_0(A_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_18])).

tff(c_1094,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k4_xboole_0(B_84,k3_xboole_0(A_83,B_84))) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1039])).

tff(c_7214,plain,(
    ! [A_171,B_172] : k3_xboole_0(A_171,k4_xboole_0(B_172,A_171)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6725,c_426])).

tff(c_7388,plain,(
    ! [B_84,A_83] : k3_xboole_0(k4_xboole_0(B_84,k3_xboole_0(A_83,B_84)),A_83) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_7214])).

tff(c_35905,plain,(
    ! [B_368] : k3_xboole_0(k4_xboole_0(k3_xboole_0('#skF_4',k4_xboole_0(B_368,'#skF_5')),k1_xboole_0),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_35842,c_7388])).

tff(c_36535,plain,(
    ! [B_372] : k3_xboole_0('#skF_4',k3_xboole_0(k4_xboole_0(B_372,'#skF_5'),'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15364,c_16,c_35905])).

tff(c_36688,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18700,c_36535])).

tff(c_60,plain,(
    ! [A_35,B_36] : r1_xboole_0(k4_xboole_0(A_35,B_36),B_36) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_63,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_60])).

tff(c_235,plain,(
    ! [A_11,C_52] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_228])).

tff(c_238,plain,(
    ! [C_52] : ~ r2_hidden(C_52,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_235])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1027,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83,k4_xboole_0(B_84,k3_xboole_0(A_83,B_84))),k1_xboole_0)
      | r1_xboole_0(A_83,k4_xboole_0(B_84,k3_xboole_0(A_83,B_84))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_4])).

tff(c_1092,plain,(
    ! [A_83,B_84] : r1_xboole_0(A_83,k4_xboole_0(B_84,k3_xboole_0(A_83,B_84))) ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_1027])).

tff(c_36923,plain,(
    r1_xboole_0('#skF_4',k4_xboole_0(k4_xboole_0('#skF_3','#skF_5'),k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36688,c_1092])).

tff(c_36998,plain,(
    r1_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_36923])).

tff(c_37000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_36998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:00:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.44/4.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.56/4.87  
% 10.56/4.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.56/4.87  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 10.56/4.87  
% 10.56/4.87  %Foreground sorts:
% 10.56/4.87  
% 10.56/4.87  
% 10.56/4.87  %Background operators:
% 10.56/4.87  
% 10.56/4.87  
% 10.56/4.87  %Foreground operators:
% 10.56/4.87  tff('#skF_2', type, '#skF_2': $i > $i).
% 10.56/4.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.56/4.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.56/4.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.56/4.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.56/4.87  tff('#skF_5', type, '#skF_5': $i).
% 10.56/4.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.56/4.87  tff('#skF_3', type, '#skF_3': $i).
% 10.56/4.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.56/4.87  tff('#skF_4', type, '#skF_4': $i).
% 10.56/4.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.56/4.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.56/4.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.56/4.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.56/4.87  
% 10.61/4.89  tff(f_76, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 10.61/4.89  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.61/4.89  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.61/4.89  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.61/4.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.61/4.89  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.61/4.89  tff(f_63, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 10.61/4.89  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 10.61/4.89  tff(f_71, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 10.61/4.89  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.61/4.89  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.61/4.89  tff(f_67, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 10.61/4.89  tff(f_65, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 10.61/4.89  tff(f_69, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 10.61/4.89  tff(c_32, plain, (~r1_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.61/4.89  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.61/4.89  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.61/4.89  tff(c_246, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k4_xboole_0(A_54, B_55))=k3_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.61/4.89  tff(c_276, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_246])).
% 10.61/4.89  tff(c_284, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_276])).
% 10.61/4.89  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.61/4.89  tff(c_289, plain, (![A_56]: (k4_xboole_0(A_56, k1_xboole_0)=k3_xboole_0(A_56, A_56))), inference(superposition, [status(thm), theory('equality')], [c_284, c_20])).
% 10.61/4.89  tff(c_313, plain, (![A_56]: (k3_xboole_0(A_56, A_56)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_289])).
% 10.61/4.89  tff(c_65, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.61/4.89  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.61/4.89  tff(c_81, plain, (![A_39]: (k2_xboole_0(k1_xboole_0, A_39)=A_39)), inference(superposition, [status(thm), theory('equality')], [c_65, c_10])).
% 10.61/4.89  tff(c_22, plain, (![A_19, B_20, C_21]: (k4_xboole_0(k3_xboole_0(A_19, B_20), C_21)=k3_xboole_0(A_19, k4_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.61/4.89  tff(c_176, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.61/4.89  tff(c_30, plain, (![A_30, B_31]: (r1_xboole_0(k4_xboole_0(A_30, B_31), B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.61/4.89  tff(c_185, plain, (![A_44, B_45]: (r1_xboole_0(k4_xboole_0(A_44, B_45), k3_xboole_0(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_176, c_30])).
% 10.61/4.89  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.61/4.89  tff(c_228, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, k3_xboole_0(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.61/4.89  tff(c_406, plain, (![A_64, B_65]: (~r1_xboole_0(A_64, B_65) | k3_xboole_0(A_64, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_228])).
% 10.61/4.89  tff(c_423, plain, (![A_44, B_45]: (k3_xboole_0(k4_xboole_0(A_44, B_45), k3_xboole_0(A_44, B_45))=k1_xboole_0)), inference(resolution, [status(thm)], [c_185, c_406])).
% 10.61/4.89  tff(c_647, plain, (![A_70, B_71, C_72]: (k4_xboole_0(k3_xboole_0(A_70, B_71), C_72)=k3_xboole_0(A_70, k4_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.61/4.89  tff(c_707, plain, (![A_70, B_71, B_18]: (k3_xboole_0(A_70, k4_xboole_0(B_71, k4_xboole_0(k3_xboole_0(A_70, B_71), B_18)))=k3_xboole_0(k3_xboole_0(A_70, B_71), B_18))), inference(superposition, [status(thm), theory('equality')], [c_20, c_647])).
% 10.61/4.89  tff(c_17375, plain, (![A_258, B_259, B_260]: (k3_xboole_0(A_258, k4_xboole_0(B_259, k3_xboole_0(A_258, k4_xboole_0(B_259, B_260))))=k3_xboole_0(k3_xboole_0(A_258, B_259), B_260))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_707])).
% 10.61/4.89  tff(c_17818, plain, (![B_259, B_260]: (k3_xboole_0(k4_xboole_0(B_259, B_260), k4_xboole_0(B_259, k4_xboole_0(B_259, B_260)))=k3_xboole_0(k3_xboole_0(k4_xboole_0(B_259, B_260), B_259), B_260))), inference(superposition, [status(thm), theory('equality')], [c_313, c_17375])).
% 10.61/4.89  tff(c_18308, plain, (![B_263, B_264]: (k3_xboole_0(k3_xboole_0(k4_xboole_0(B_263, B_264), B_263), B_264)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_423, c_20, c_17818])).
% 10.61/4.89  tff(c_26, plain, (![A_25, B_26]: (k2_xboole_0(k3_xboole_0(A_25, B_26), k4_xboole_0(A_25, B_26))=A_25)), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.61/4.89  tff(c_18510, plain, (![B_263, B_264]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(k3_xboole_0(k4_xboole_0(B_263, B_264), B_263), B_264))=k3_xboole_0(k4_xboole_0(B_263, B_264), B_263))), inference(superposition, [status(thm), theory('equality')], [c_18308, c_26])).
% 10.61/4.89  tff(c_18700, plain, (![B_263, B_264]: (k3_xboole_0(k4_xboole_0(B_263, B_264), B_263)=k4_xboole_0(B_263, B_264))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_81, c_22, c_18510])).
% 10.61/4.89  tff(c_1617, plain, (![A_99, B_100, C_101]: (k4_xboole_0(k3_xboole_0(A_99, B_100), k3_xboole_0(A_99, C_101))=k3_xboole_0(A_99, k4_xboole_0(B_100, C_101)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.61/4.89  tff(c_1649, plain, (![A_99, B_100, C_101]: (k3_xboole_0(A_99, k4_xboole_0(B_100, k3_xboole_0(A_99, C_101)))=k3_xboole_0(A_99, k4_xboole_0(B_100, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_1617, c_22])).
% 10.61/4.89  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.61/4.89  tff(c_273, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, k3_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_246])).
% 10.61/4.89  tff(c_282, plain, (![A_15, B_16]: (k3_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_273])).
% 10.61/4.89  tff(c_14861, plain, (![A_245, B_246, C_247]: (k4_xboole_0(k3_xboole_0(A_245, B_246), k3_xboole_0(A_245, k4_xboole_0(B_246, C_247)))=k3_xboole_0(k3_xboole_0(A_245, B_246), C_247))), inference(superposition, [status(thm), theory('equality')], [c_647, c_20])).
% 10.61/4.89  tff(c_15215, plain, (![A_15, B_16, C_247]: (k4_xboole_0(k3_xboole_0(A_15, B_16), k3_xboole_0(A_15, k4_xboole_0(k3_xboole_0(A_15, B_16), C_247)))=k3_xboole_0(k3_xboole_0(A_15, k3_xboole_0(A_15, B_16)), C_247))), inference(superposition, [status(thm), theory('equality')], [c_282, c_14861])).
% 10.61/4.89  tff(c_15364, plain, (![A_15, B_16, C_247]: (k3_xboole_0(k3_xboole_0(A_15, B_16), C_247)=k3_xboole_0(A_15, k3_xboole_0(B_16, C_247)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1649, c_282, c_282, c_22, c_22, c_15215])).
% 10.61/4.89  tff(c_35070, plain, (![A_364, B_365, C_366]: (k3_xboole_0(k3_xboole_0(A_364, B_365), C_366)=k3_xboole_0(A_364, k3_xboole_0(B_365, C_366)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1649, c_282, c_282, c_22, c_22, c_15215])).
% 10.61/4.89  tff(c_267, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k3_xboole_0(A_17, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_246])).
% 10.61/4.89  tff(c_280, plain, (![A_17, B_18]: (k3_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_267])).
% 10.61/4.89  tff(c_301, plain, (![A_56]: (r1_xboole_0(k1_xboole_0, A_56))), inference(superposition, [status(thm), theory('equality')], [c_284, c_30])).
% 10.61/4.89  tff(c_453, plain, (![A_66]: (k3_xboole_0(k1_xboole_0, A_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_301, c_406])).
% 10.61/4.89  tff(c_474, plain, (![A_66]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_66))), inference(superposition, [status(thm), theory('equality')], [c_453, c_18])).
% 10.61/4.89  tff(c_494, plain, (![A_66]: (k4_xboole_0(k1_xboole_0, A_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_474])).
% 10.61/4.89  tff(c_1159, plain, (![A_87, B_88, C_89]: (k2_xboole_0(k4_xboole_0(A_87, B_88), k3_xboole_0(A_87, C_89))=k4_xboole_0(A_87, k4_xboole_0(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.61/4.89  tff(c_1222, plain, (![A_14, C_89]: (k4_xboole_0(A_14, k4_xboole_0(k1_xboole_0, C_89))=k2_xboole_0(A_14, k3_xboole_0(A_14, C_89)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1159])).
% 10.61/4.89  tff(c_1237, plain, (![A_90, C_91]: (k2_xboole_0(A_90, k3_xboole_0(A_90, C_91))=A_90)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_494, c_1222])).
% 10.61/4.89  tff(c_1256, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(A_17, B_18))=A_17)), inference(superposition, [status(thm), theory('equality')], [c_280, c_1237])).
% 10.61/4.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.61/4.89  tff(c_6389, plain, (![A_159, C_160, B_161]: (k2_xboole_0(k3_xboole_0(A_159, C_160), k4_xboole_0(A_159, B_161))=k4_xboole_0(A_159, k4_xboole_0(B_161, C_160)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1159])).
% 10.61/4.89  tff(c_6514, plain, (![A_56, B_161]: (k4_xboole_0(A_56, k4_xboole_0(B_161, A_56))=k2_xboole_0(A_56, k4_xboole_0(A_56, B_161)))), inference(superposition, [status(thm), theory('equality')], [c_313, c_6389])).
% 10.61/4.89  tff(c_6725, plain, (![A_164, B_165]: (k4_xboole_0(A_164, k4_xboole_0(B_165, A_164))=A_164)), inference(demodulation, [status(thm), theory('equality')], [c_1256, c_6514])).
% 10.61/4.89  tff(c_426, plain, (![A_30, B_31]: (k3_xboole_0(k4_xboole_0(A_30, B_31), B_31)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_406])).
% 10.61/4.89  tff(c_6839, plain, (![A_164, B_165]: (k3_xboole_0(A_164, k4_xboole_0(B_165, A_164))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6725, c_426])).
% 10.61/4.89  tff(c_34, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.61/4.89  tff(c_427, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_406])).
% 10.61/4.89  tff(c_13264, plain, (![A_236, B_237, C_238]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_236, B_237), C_238), k3_xboole_0(A_236, k4_xboole_0(B_237, C_238)))=k3_xboole_0(A_236, B_237))), inference(superposition, [status(thm), theory('equality')], [c_647, c_26])).
% 10.61/4.89  tff(c_13537, plain, (k2_xboole_0(k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), '#skF_5'), k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_427, c_13264])).
% 10.61/4.89  tff(c_14464, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), '#skF_5')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13537, c_10])).
% 10.61/4.89  tff(c_14533, plain, (![B_100]: (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k4_xboole_0(B_100, k3_xboole_0('#skF_3', '#skF_4')))=k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k4_xboole_0(B_100, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_14464, c_1649])).
% 10.61/4.89  tff(c_14602, plain, (![B_100]: (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k4_xboole_0(B_100, '#skF_5'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6839, c_14533])).
% 10.61/4.89  tff(c_35842, plain, (![B_368]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', k4_xboole_0(B_368, '#skF_5')))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_35070, c_14602])).
% 10.61/4.89  tff(c_283, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_276])).
% 10.61/4.89  tff(c_1000, plain, (![A_83, B_84]: (k3_xboole_0(A_83, k4_xboole_0(B_84, k3_xboole_0(A_83, B_84)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_283, c_647])).
% 10.61/4.89  tff(c_1039, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k4_xboole_0(B_84, k3_xboole_0(A_83, B_84)))=k4_xboole_0(A_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1000, c_18])).
% 10.61/4.89  tff(c_1094, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k4_xboole_0(B_84, k3_xboole_0(A_83, B_84)))=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1039])).
% 10.61/4.89  tff(c_7214, plain, (![A_171, B_172]: (k3_xboole_0(A_171, k4_xboole_0(B_172, A_171))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6725, c_426])).
% 10.61/4.89  tff(c_7388, plain, (![B_84, A_83]: (k3_xboole_0(k4_xboole_0(B_84, k3_xboole_0(A_83, B_84)), A_83)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1094, c_7214])).
% 10.61/4.89  tff(c_35905, plain, (![B_368]: (k3_xboole_0(k4_xboole_0(k3_xboole_0('#skF_4', k4_xboole_0(B_368, '#skF_5')), k1_xboole_0), '#skF_3')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_35842, c_7388])).
% 10.61/4.89  tff(c_36535, plain, (![B_372]: (k3_xboole_0('#skF_4', k3_xboole_0(k4_xboole_0(B_372, '#skF_5'), '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_15364, c_16, c_35905])).
% 10.61/4.89  tff(c_36688, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18700, c_36535])).
% 10.61/4.89  tff(c_60, plain, (![A_35, B_36]: (r1_xboole_0(k4_xboole_0(A_35, B_36), B_36))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.61/4.89  tff(c_63, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_60])).
% 10.61/4.89  tff(c_235, plain, (![A_11, C_52]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_228])).
% 10.61/4.89  tff(c_238, plain, (![C_52]: (~r2_hidden(C_52, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_235])).
% 10.61/4.89  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.61/4.89  tff(c_1027, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83, k4_xboole_0(B_84, k3_xboole_0(A_83, B_84))), k1_xboole_0) | r1_xboole_0(A_83, k4_xboole_0(B_84, k3_xboole_0(A_83, B_84))))), inference(superposition, [status(thm), theory('equality')], [c_1000, c_4])).
% 10.61/4.89  tff(c_1092, plain, (![A_83, B_84]: (r1_xboole_0(A_83, k4_xboole_0(B_84, k3_xboole_0(A_83, B_84))))), inference(negUnitSimplification, [status(thm)], [c_238, c_1027])).
% 10.61/4.89  tff(c_36923, plain, (r1_xboole_0('#skF_4', k4_xboole_0(k4_xboole_0('#skF_3', '#skF_5'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36688, c_1092])).
% 10.61/4.89  tff(c_36998, plain, (r1_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_36923])).
% 10.61/4.89  tff(c_37000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_36998])).
% 10.61/4.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.61/4.89  
% 10.61/4.89  Inference rules
% 10.61/4.89  ----------------------
% 10.61/4.89  #Ref     : 0
% 10.61/4.89  #Sup     : 9261
% 10.61/4.89  #Fact    : 0
% 10.61/4.89  #Define  : 0
% 10.61/4.89  #Split   : 0
% 10.61/4.89  #Chain   : 0
% 10.61/4.89  #Close   : 0
% 10.61/4.89  
% 10.61/4.89  Ordering : KBO
% 10.61/4.89  
% 10.61/4.89  Simplification rules
% 10.61/4.89  ----------------------
% 10.61/4.89  #Subsume      : 46
% 10.61/4.89  #Demod        : 10951
% 10.61/4.89  #Tautology    : 6601
% 10.61/4.89  #SimpNegUnit  : 44
% 10.61/4.89  #BackRed      : 18
% 10.61/4.89  
% 10.61/4.89  #Partial instantiations: 0
% 10.61/4.89  #Strategies tried      : 1
% 10.61/4.89  
% 10.61/4.89  Timing (in seconds)
% 10.61/4.89  ----------------------
% 10.61/4.89  Preprocessing        : 0.29
% 10.61/4.89  Parsing              : 0.16
% 10.61/4.89  CNF conversion       : 0.02
% 10.61/4.90  Main loop            : 3.83
% 10.61/4.90  Inferencing          : 0.71
% 10.61/4.90  Reduction            : 2.25
% 10.61/4.90  Demodulation         : 2.01
% 10.61/4.90  BG Simplification    : 0.08
% 10.61/4.90  Subsumption          : 0.63
% 10.61/4.90  Abstraction          : 0.15
% 10.61/4.90  MUC search           : 0.00
% 10.61/4.90  Cooper               : 0.00
% 10.61/4.90  Total                : 4.17
% 10.61/4.90  Index Insertion      : 0.00
% 10.61/4.90  Index Deletion       : 0.00
% 10.61/4.90  Index Matching       : 0.00
% 10.61/4.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
