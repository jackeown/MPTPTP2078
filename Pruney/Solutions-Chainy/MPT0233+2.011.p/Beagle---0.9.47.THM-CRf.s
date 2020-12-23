%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:25 EST 2020

% Result     : Theorem 6.29s
% Output     : CNFRefutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 175 expanded)
%              Number of leaves         :   42 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  102 ( 190 expanded)
%              Number of equality atoms :   76 ( 142 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_68,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_70,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56,plain,(
    ! [A_40,B_41,C_42] : k2_enumset1(A_40,A_40,B_41,C_42) = k1_enumset1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2070,plain,(
    ! [A_173,B_174,C_175,D_176] : k2_xboole_0(k1_enumset1(A_173,B_174,C_175),k1_tarski(D_176)) = k2_enumset1(A_173,B_174,C_175,D_176) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2085,plain,(
    ! [A_38,B_39,D_176] : k2_xboole_0(k2_tarski(A_38,B_39),k1_tarski(D_176)) = k2_enumset1(A_38,A_38,B_39,D_176) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2070])).

tff(c_2094,plain,(
    ! [A_38,B_39,D_176] : k2_xboole_0(k2_tarski(A_38,B_39),k1_tarski(D_176)) = k1_enumset1(A_38,B_39,D_176) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2085])).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7932,plain,(
    ! [A_321,B_322,D_323] : k2_xboole_0(k2_tarski(A_321,B_322),k1_tarski(D_323)) = k1_enumset1(A_321,B_322,D_323) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2085])).

tff(c_7953,plain,(
    ! [A_37,D_323] : k2_xboole_0(k1_tarski(A_37),k1_tarski(D_323)) = k1_enumset1(A_37,A_37,D_323) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_7932])).

tff(c_8664,plain,(
    ! [A_343,D_344] : k2_xboole_0(k1_tarski(A_343),k1_tarski(D_344)) = k2_tarski(A_343,D_344) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_7953])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8932,plain,(
    ! [D_350,A_351] : k2_xboole_0(k1_tarski(D_350),k1_tarski(A_351)) = k2_tarski(A_351,D_350) ),
    inference(superposition,[status(thm),theory(equality)],[c_8664,c_2])).

tff(c_7956,plain,(
    ! [A_37,D_323] : k2_xboole_0(k1_tarski(A_37),k1_tarski(D_323)) = k2_tarski(A_37,D_323) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_7953])).

tff(c_8938,plain,(
    ! [D_350,A_351] : k2_tarski(D_350,A_351) = k2_tarski(A_351,D_350) ),
    inference(superposition,[status(thm),theory(equality)],[c_8932,c_7956])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [A_65,B_66] : r1_tarski(k1_tarski(A_65),k2_tarski(A_65,B_66)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_316,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(A_94,B_95) = A_94
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1186,plain,(
    ! [A_144,B_145] : k3_xboole_0(k1_tarski(A_144),k2_tarski(A_144,B_145)) = k1_tarski(A_144) ),
    inference(resolution,[status(thm)],[c_66,c_316])).

tff(c_72,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_339,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) = k2_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_316])).

tff(c_140,plain,(
    ! [B_81,A_82] : k3_xboole_0(B_81,A_82) = k3_xboole_0(A_82,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_163,plain,(
    ! [B_81,A_82] : r1_tarski(k3_xboole_0(B_81,A_82),A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_10])).

tff(c_393,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_tarski(A_105,B_106)
      | ~ r1_tarski(A_105,k3_xboole_0(B_106,C_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_515,plain,(
    ! [B_113,B_114,C_115] : r1_tarski(k3_xboole_0(B_113,k3_xboole_0(B_114,C_115)),B_114) ),
    inference(resolution,[status(thm)],[c_163,c_393])).

tff(c_685,plain,(
    ! [B_122,B_123,A_124] : r1_tarski(k3_xboole_0(B_122,k3_xboole_0(B_123,A_124)),A_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_515])).

tff(c_702,plain,(
    ! [B_122] : r1_tarski(k3_xboole_0(B_122,k2_tarski('#skF_3','#skF_4')),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_685])).

tff(c_1199,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_702])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1241,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_1199,c_14])).

tff(c_105,plain,(
    ! [A_73] :
      ( k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_116,plain,(
    ! [B_10] : k3_xboole_0(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_105])).

tff(c_156,plain,(
    ! [B_81] : k3_xboole_0(B_81,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_116])).

tff(c_751,plain,(
    ! [A_125,B_126] : k5_xboole_0(A_125,k3_xboole_0(A_125,B_126)) = k4_xboole_0(A_125,B_126) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_763,plain,(
    ! [B_81] : k5_xboole_0(B_81,k1_xboole_0) = k4_xboole_0(B_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_751])).

tff(c_805,plain,(
    ! [B_128] : k4_xboole_0(B_128,k1_xboole_0) = B_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_763])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_815,plain,(
    ! [B_128] : k4_xboole_0(B_128,B_128) = k3_xboole_0(B_128,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_18])).

tff(c_828,plain,(
    ! [B_128] : k4_xboole_0(B_128,B_128) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_815])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_775,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_751])).

tff(c_989,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_775])).

tff(c_1270,plain,(
    ! [A_152,B_153] : k3_xboole_0(k3_xboole_0(A_152,B_153),A_152) = k3_xboole_0(A_152,B_153) ),
    inference(resolution,[status(thm)],[c_10,c_316])).

tff(c_1289,plain,(
    ! [A_152,B_153] : k5_xboole_0(k3_xboole_0(A_152,B_153),k3_xboole_0(A_152,B_153)) = k4_xboole_0(k3_xboole_0(A_152,B_153),A_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_8])).

tff(c_1378,plain,(
    ! [A_152,B_153] : k4_xboole_0(k3_xboole_0(A_152,B_153),A_152) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_989,c_1289])).

tff(c_2096,plain,(
    ! [B_177,A_178] : k3_xboole_0(k3_xboole_0(B_177,A_178),A_178) = k3_xboole_0(B_177,A_178) ),
    inference(resolution,[status(thm)],[c_163,c_316])).

tff(c_2916,plain,(
    ! [A_199,B_200] : k3_xboole_0(k3_xboole_0(A_199,B_200),A_199) = k3_xboole_0(B_200,A_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2096])).

tff(c_2988,plain,(
    ! [A_199,B_200] : k5_xboole_0(k3_xboole_0(A_199,B_200),k3_xboole_0(B_200,A_199)) = k4_xboole_0(k3_xboole_0(A_199,B_200),A_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_2916,c_8])).

tff(c_3120,plain,(
    ! [A_199,B_200] : k5_xboole_0(k3_xboole_0(A_199,B_200),k3_xboole_0(B_200,A_199)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1378,c_2988])).

tff(c_4326,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_3'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_3120])).

tff(c_4419,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4,c_4326])).

tff(c_8982,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8938,c_4419])).

tff(c_22,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_9469,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_5'),k1_tarski('#skF_3')) = k5_xboole_0(k2_tarski('#skF_6','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8982,c_22])).

tff(c_9482,plain,(
    k1_enumset1('#skF_6','#skF_5','#skF_3') = k2_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2094,c_20,c_9469])).

tff(c_26,plain,(
    ! [E_28,A_22,B_23] : r2_hidden(E_28,k1_enumset1(A_22,B_23,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_9499,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9482,c_26])).

tff(c_1633,plain,(
    ! [E_163,C_164,B_165,A_166] :
      ( E_163 = C_164
      | E_163 = B_165
      | E_163 = A_166
      | ~ r2_hidden(E_163,k1_enumset1(A_166,B_165,C_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1636,plain,(
    ! [E_163,B_39,A_38] :
      ( E_163 = B_39
      | E_163 = A_38
      | E_163 = A_38
      | ~ r2_hidden(E_163,k2_tarski(A_38,B_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1633])).

tff(c_9512,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9499,c_1636])).

tff(c_9516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_70,c_9512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.29/2.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.34  
% 6.29/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.34  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 6.29/2.34  
% 6.29/2.34  %Foreground sorts:
% 6.29/2.34  
% 6.29/2.34  
% 6.29/2.34  %Background operators:
% 6.29/2.34  
% 6.29/2.34  
% 6.29/2.34  %Foreground operators:
% 6.29/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.29/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.29/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.29/2.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.29/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.29/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.29/2.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.29/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.29/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.29/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.29/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.29/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.29/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.29/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.29/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.29/2.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.29/2.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.29/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.29/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.29/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.29/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.29/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.29/2.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.29/2.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.29/2.34  
% 6.42/2.36  tff(f_98, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 6.42/2.36  tff(f_78, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.42/2.36  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.42/2.36  tff(f_72, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 6.42/2.36  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.42/2.36  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.42/2.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.42/2.36  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.42/2.36  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.42/2.36  tff(f_88, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 6.42/2.36  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.42/2.36  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.42/2.36  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 6.42/2.36  tff(f_47, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.42/2.36  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.42/2.36  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.42/2.36  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.42/2.36  tff(f_68, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.42/2.36  tff(c_68, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.42/2.36  tff(c_70, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.42/2.36  tff(c_56, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, A_40, B_41, C_42)=k1_enumset1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.42/2.36  tff(c_54, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.42/2.36  tff(c_2070, plain, (![A_173, B_174, C_175, D_176]: (k2_xboole_0(k1_enumset1(A_173, B_174, C_175), k1_tarski(D_176))=k2_enumset1(A_173, B_174, C_175, D_176))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.42/2.36  tff(c_2085, plain, (![A_38, B_39, D_176]: (k2_xboole_0(k2_tarski(A_38, B_39), k1_tarski(D_176))=k2_enumset1(A_38, A_38, B_39, D_176))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2070])).
% 6.42/2.36  tff(c_2094, plain, (![A_38, B_39, D_176]: (k2_xboole_0(k2_tarski(A_38, B_39), k1_tarski(D_176))=k1_enumset1(A_38, B_39, D_176))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2085])).
% 6.42/2.36  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.42/2.36  tff(c_52, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.42/2.36  tff(c_7932, plain, (![A_321, B_322, D_323]: (k2_xboole_0(k2_tarski(A_321, B_322), k1_tarski(D_323))=k1_enumset1(A_321, B_322, D_323))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2085])).
% 6.42/2.36  tff(c_7953, plain, (![A_37, D_323]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(D_323))=k1_enumset1(A_37, A_37, D_323))), inference(superposition, [status(thm), theory('equality')], [c_52, c_7932])).
% 6.42/2.36  tff(c_8664, plain, (![A_343, D_344]: (k2_xboole_0(k1_tarski(A_343), k1_tarski(D_344))=k2_tarski(A_343, D_344))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_7953])).
% 6.42/2.36  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.42/2.36  tff(c_8932, plain, (![D_350, A_351]: (k2_xboole_0(k1_tarski(D_350), k1_tarski(A_351))=k2_tarski(A_351, D_350))), inference(superposition, [status(thm), theory('equality')], [c_8664, c_2])).
% 6.42/2.36  tff(c_7956, plain, (![A_37, D_323]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(D_323))=k2_tarski(A_37, D_323))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_7953])).
% 6.42/2.36  tff(c_8938, plain, (![D_350, A_351]: (k2_tarski(D_350, A_351)=k2_tarski(A_351, D_350))), inference(superposition, [status(thm), theory('equality')], [c_8932, c_7956])).
% 6.42/2.36  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.42/2.36  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.42/2.36  tff(c_66, plain, (![A_65, B_66]: (r1_tarski(k1_tarski(A_65), k2_tarski(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.42/2.36  tff(c_316, plain, (![A_94, B_95]: (k3_xboole_0(A_94, B_95)=A_94 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.42/2.36  tff(c_1186, plain, (![A_144, B_145]: (k3_xboole_0(k1_tarski(A_144), k2_tarski(A_144, B_145))=k1_tarski(A_144))), inference(resolution, [status(thm)], [c_66, c_316])).
% 6.42/2.36  tff(c_72, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.42/2.36  tff(c_339, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))=k2_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_316])).
% 6.42/2.36  tff(c_140, plain, (![B_81, A_82]: (k3_xboole_0(B_81, A_82)=k3_xboole_0(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.42/2.36  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.42/2.36  tff(c_163, plain, (![B_81, A_82]: (r1_tarski(k3_xboole_0(B_81, A_82), A_82))), inference(superposition, [status(thm), theory('equality')], [c_140, c_10])).
% 6.42/2.36  tff(c_393, plain, (![A_105, B_106, C_107]: (r1_tarski(A_105, B_106) | ~r1_tarski(A_105, k3_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.42/2.36  tff(c_515, plain, (![B_113, B_114, C_115]: (r1_tarski(k3_xboole_0(B_113, k3_xboole_0(B_114, C_115)), B_114))), inference(resolution, [status(thm)], [c_163, c_393])).
% 6.42/2.36  tff(c_685, plain, (![B_122, B_123, A_124]: (r1_tarski(k3_xboole_0(B_122, k3_xboole_0(B_123, A_124)), A_124))), inference(superposition, [status(thm), theory('equality')], [c_4, c_515])).
% 6.42/2.36  tff(c_702, plain, (![B_122]: (r1_tarski(k3_xboole_0(B_122, k2_tarski('#skF_3', '#skF_4')), k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_339, c_685])).
% 6.42/2.36  tff(c_1199, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1186, c_702])).
% 6.42/2.36  tff(c_14, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.42/2.36  tff(c_1241, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_1199, c_14])).
% 6.42/2.36  tff(c_105, plain, (![A_73]: (k1_xboole_0=A_73 | ~r1_tarski(A_73, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.42/2.36  tff(c_116, plain, (![B_10]: (k3_xboole_0(k1_xboole_0, B_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_105])).
% 6.42/2.36  tff(c_156, plain, (![B_81]: (k3_xboole_0(B_81, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_140, c_116])).
% 6.42/2.36  tff(c_751, plain, (![A_125, B_126]: (k5_xboole_0(A_125, k3_xboole_0(A_125, B_126))=k4_xboole_0(A_125, B_126))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.42/2.36  tff(c_763, plain, (![B_81]: (k5_xboole_0(B_81, k1_xboole_0)=k4_xboole_0(B_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_156, c_751])).
% 6.42/2.36  tff(c_805, plain, (![B_128]: (k4_xboole_0(B_128, k1_xboole_0)=B_128)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_763])).
% 6.42/2.36  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.42/2.36  tff(c_815, plain, (![B_128]: (k4_xboole_0(B_128, B_128)=k3_xboole_0(B_128, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_805, c_18])).
% 6.42/2.36  tff(c_828, plain, (![B_128]: (k4_xboole_0(B_128, B_128)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_815])).
% 6.42/2.36  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.42/2.36  tff(c_775, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_751])).
% 6.42/2.36  tff(c_989, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_828, c_775])).
% 6.42/2.36  tff(c_1270, plain, (![A_152, B_153]: (k3_xboole_0(k3_xboole_0(A_152, B_153), A_152)=k3_xboole_0(A_152, B_153))), inference(resolution, [status(thm)], [c_10, c_316])).
% 6.42/2.36  tff(c_1289, plain, (![A_152, B_153]: (k5_xboole_0(k3_xboole_0(A_152, B_153), k3_xboole_0(A_152, B_153))=k4_xboole_0(k3_xboole_0(A_152, B_153), A_152))), inference(superposition, [status(thm), theory('equality')], [c_1270, c_8])).
% 6.42/2.36  tff(c_1378, plain, (![A_152, B_153]: (k4_xboole_0(k3_xboole_0(A_152, B_153), A_152)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_989, c_1289])).
% 6.42/2.36  tff(c_2096, plain, (![B_177, A_178]: (k3_xboole_0(k3_xboole_0(B_177, A_178), A_178)=k3_xboole_0(B_177, A_178))), inference(resolution, [status(thm)], [c_163, c_316])).
% 6.42/2.36  tff(c_2916, plain, (![A_199, B_200]: (k3_xboole_0(k3_xboole_0(A_199, B_200), A_199)=k3_xboole_0(B_200, A_199))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2096])).
% 6.42/2.36  tff(c_2988, plain, (![A_199, B_200]: (k5_xboole_0(k3_xboole_0(A_199, B_200), k3_xboole_0(B_200, A_199))=k4_xboole_0(k3_xboole_0(A_199, B_200), A_199))), inference(superposition, [status(thm), theory('equality')], [c_2916, c_8])).
% 6.42/2.36  tff(c_3120, plain, (![A_199, B_200]: (k5_xboole_0(k3_xboole_0(A_199, B_200), k3_xboole_0(B_200, A_199))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1378, c_2988])).
% 6.42/2.36  tff(c_4326, plain, (k5_xboole_0(k1_tarski('#skF_3'), k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_3')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1241, c_3120])).
% 6.42/2.36  tff(c_4419, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4, c_4326])).
% 6.42/2.36  tff(c_8982, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_6', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8938, c_4419])).
% 6.42/2.36  tff(c_22, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.42/2.36  tff(c_9469, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), k1_tarski('#skF_3'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8982, c_22])).
% 6.42/2.36  tff(c_9482, plain, (k1_enumset1('#skF_6', '#skF_5', '#skF_3')=k2_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2094, c_20, c_9469])).
% 6.42/2.36  tff(c_26, plain, (![E_28, A_22, B_23]: (r2_hidden(E_28, k1_enumset1(A_22, B_23, E_28)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.42/2.36  tff(c_9499, plain, (r2_hidden('#skF_3', k2_tarski('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9482, c_26])).
% 6.42/2.36  tff(c_1633, plain, (![E_163, C_164, B_165, A_166]: (E_163=C_164 | E_163=B_165 | E_163=A_166 | ~r2_hidden(E_163, k1_enumset1(A_166, B_165, C_164)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.42/2.36  tff(c_1636, plain, (![E_163, B_39, A_38]: (E_163=B_39 | E_163=A_38 | E_163=A_38 | ~r2_hidden(E_163, k2_tarski(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1633])).
% 6.42/2.36  tff(c_9512, plain, ('#skF_5'='#skF_3' | '#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_9499, c_1636])).
% 6.42/2.36  tff(c_9516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_70, c_9512])).
% 6.42/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.36  
% 6.42/2.36  Inference rules
% 6.42/2.36  ----------------------
% 6.42/2.36  #Ref     : 0
% 6.42/2.36  #Sup     : 2251
% 6.42/2.36  #Fact    : 0
% 6.42/2.36  #Define  : 0
% 6.42/2.36  #Split   : 0
% 6.42/2.36  #Chain   : 0
% 6.42/2.36  #Close   : 0
% 6.42/2.36  
% 6.42/2.36  Ordering : KBO
% 6.42/2.36  
% 6.42/2.36  Simplification rules
% 6.42/2.36  ----------------------
% 6.42/2.36  #Subsume      : 51
% 6.42/2.36  #Demod        : 2363
% 6.42/2.36  #Tautology    : 1740
% 6.42/2.36  #SimpNegUnit  : 1
% 6.42/2.36  #BackRed      : 23
% 6.42/2.36  
% 6.42/2.36  #Partial instantiations: 0
% 6.42/2.36  #Strategies tried      : 1
% 6.42/2.36  
% 6.42/2.36  Timing (in seconds)
% 6.42/2.36  ----------------------
% 6.42/2.37  Preprocessing        : 0.35
% 6.42/2.37  Parsing              : 0.19
% 6.42/2.37  CNF conversion       : 0.02
% 6.42/2.37  Main loop            : 1.20
% 6.42/2.37  Inferencing          : 0.32
% 6.42/2.37  Reduction            : 0.59
% 6.42/2.37  Demodulation         : 0.49
% 6.42/2.37  BG Simplification    : 0.04
% 6.42/2.37  Subsumption          : 0.18
% 6.42/2.37  Abstraction          : 0.05
% 6.42/2.37  MUC search           : 0.00
% 6.42/2.37  Cooper               : 0.00
% 6.42/2.37  Total                : 1.58
% 6.42/2.37  Index Insertion      : 0.00
% 6.42/2.37  Index Deletion       : 0.00
% 6.42/2.37  Index Matching       : 0.00
% 6.42/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
