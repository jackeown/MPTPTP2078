%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:30 EST 2020

% Result     : Theorem 22.06s
% Output     : CNFRefutation 22.06s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 196 expanded)
%              Number of leaves         :   38 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :   87 ( 182 expanded)
%              Number of equality atoms :   75 ( 169 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_44,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_136,plain,(
    ! [B_61,A_62] : k5_xboole_0(B_61,A_62) = k5_xboole_0(A_62,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152,plain,(
    ! [A_62] : k5_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_14])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_440,plain,(
    ! [A_93,B_94] : k5_xboole_0(k5_xboole_0(A_93,B_94),k2_xboole_0(A_93,B_94)) = k3_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_492,plain,(
    ! [A_9] : k5_xboole_0(k5_xboole_0(A_9,k1_xboole_0),A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_440])).

tff(c_501,plain,(
    ! [A_95] : k5_xboole_0(A_95,A_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_492])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k5_xboole_0(k5_xboole_0(A_12,B_13),C_14) = k5_xboole_0(A_12,k5_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_509,plain,(
    ! [A_95,C_14] : k5_xboole_0(A_95,k5_xboole_0(A_95,C_14)) = k5_xboole_0(k1_xboole_0,C_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_16])).

tff(c_538,plain,(
    ! [A_95,C_14] : k5_xboole_0(A_95,k5_xboole_0(A_95,C_14)) = C_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_509])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_254,plain,(
    ! [C_69,B_70,A_71] : k1_enumset1(C_69,B_70,A_71) = k1_enumset1(A_71,B_70,C_69) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_270,plain,(
    ! [C_69,B_70] : k1_enumset1(C_69,B_70,B_70) = k2_tarski(B_70,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_28])).

tff(c_26,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [A_37,B_38,C_39,D_40] : k3_enumset1(A_37,A_37,B_38,C_39,D_40) = k2_enumset1(A_37,B_38,C_39,D_40) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_947,plain,(
    ! [B_118,A_117,D_119,C_116,E_120] : k2_xboole_0(k1_enumset1(A_117,B_118,C_116),k2_tarski(D_119,E_120)) = k3_enumset1(A_117,B_118,C_116,D_119,E_120) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_968,plain,(
    ! [A_32,B_33,D_119,E_120] : k3_enumset1(A_32,A_32,B_33,D_119,E_120) = k2_xboole_0(k2_tarski(A_32,B_33),k2_tarski(D_119,E_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_947])).

tff(c_4565,plain,(
    ! [A_163,B_164,D_165,E_166] : k2_xboole_0(k2_tarski(A_163,B_164),k2_tarski(D_165,E_166)) = k2_enumset1(A_163,B_164,D_165,E_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_968])).

tff(c_4596,plain,(
    ! [A_31,D_165,E_166] : k2_xboole_0(k1_tarski(A_31),k2_tarski(D_165,E_166)) = k2_enumset1(A_31,A_31,D_165,E_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4565])).

tff(c_5425,plain,(
    ! [A_173,D_174,E_175] : k2_xboole_0(k1_tarski(A_173),k2_tarski(D_174,E_175)) = k1_enumset1(A_173,D_174,E_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4596])).

tff(c_5452,plain,(
    ! [A_173,A_31] : k2_xboole_0(k1_tarski(A_173),k1_tarski(A_31)) = k1_enumset1(A_173,A_31,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_5425])).

tff(c_5455,plain,(
    ! [A_173,A_31] : k2_xboole_0(k1_tarski(A_173),k1_tarski(A_31)) = k2_tarski(A_31,A_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_5452])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4607,plain,(
    ! [D_167,E_168] : k2_enumset1(D_167,E_168,D_167,E_168) = k2_tarski(D_167,E_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_4565,c_4])).

tff(c_4614,plain,(
    ! [E_168] : k1_enumset1(E_168,E_168,E_168) = k2_tarski(E_168,E_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_4607,c_30])).

tff(c_4623,plain,(
    ! [E_168] : k1_enumset1(E_168,E_168,E_168) = k1_tarski(E_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4614])).

tff(c_34,plain,(
    ! [D_44,C_43,A_41,B_42,E_45] : k4_enumset1(A_41,A_41,B_42,C_43,D_44,E_45) = k3_enumset1(A_41,B_42,C_43,D_44,E_45) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1137,plain,(
    ! [C_126,F_127,E_129,D_124,A_125,B_128] : k2_xboole_0(k3_enumset1(A_125,B_128,C_126,D_124,E_129),k1_tarski(F_127)) = k4_enumset1(A_125,B_128,C_126,D_124,E_129,F_127) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1149,plain,(
    ! [C_39,B_38,F_127,A_37,D_40] : k4_enumset1(A_37,A_37,B_38,C_39,D_40,F_127) = k2_xboole_0(k2_enumset1(A_37,B_38,C_39,D_40),k1_tarski(F_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1137])).

tff(c_5618,plain,(
    ! [D_188,F_190,A_186,C_189,B_187] : k2_xboole_0(k2_enumset1(A_186,B_187,C_189,D_188),k1_tarski(F_190)) = k3_enumset1(A_186,B_187,C_189,D_188,F_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1149])).

tff(c_5651,plain,(
    ! [A_34,B_35,C_36,F_190] : k3_enumset1(A_34,A_34,B_35,C_36,F_190) = k2_xboole_0(k1_enumset1(A_34,B_35,C_36),k1_tarski(F_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5618])).

tff(c_38419,plain,(
    ! [A_342,B_343,C_344,F_345] : k2_xboole_0(k1_enumset1(A_342,B_343,C_344),k1_tarski(F_345)) = k2_enumset1(A_342,B_343,C_344,F_345) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5651])).

tff(c_38488,plain,(
    ! [E_168,F_345] : k2_xboole_0(k1_tarski(E_168),k1_tarski(F_345)) = k2_enumset1(E_168,E_168,E_168,F_345) ),
    inference(superposition,[status(thm),theory(equality)],[c_4623,c_38419])).

tff(c_38506,plain,(
    ! [E_346,F_347] : k2_enumset1(E_346,E_346,E_346,F_347) = k2_tarski(F_347,E_346) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5455,c_38488])).

tff(c_38555,plain,(
    ! [E_348,F_349] : k1_enumset1(E_348,E_348,F_349) = k2_tarski(F_349,E_348) ),
    inference(superposition,[status(thm),theory(equality)],[c_38506,c_30])).

tff(c_38619,plain,(
    ! [F_350,E_351] : k2_tarski(F_350,E_351) = k2_tarski(E_351,F_350) ),
    inference(superposition,[status(thm),theory(equality)],[c_38555,c_28])).

tff(c_36,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_39490,plain,(
    ! [F_359,E_360] : k3_tarski(k2_tarski(F_359,E_360)) = k2_xboole_0(E_360,F_359) ),
    inference(superposition,[status(thm),theory(equality)],[c_38619,c_36])).

tff(c_39528,plain,(
    ! [F_361,E_362] : k2_xboole_0(F_361,E_362) = k2_xboole_0(E_362,F_361) ),
    inference(superposition,[status(thm),theory(equality)],[c_39490,c_36])).

tff(c_558,plain,(
    ! [A_99,C_100] : k5_xboole_0(A_99,k5_xboole_0(A_99,C_100)) = C_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_509])).

tff(c_607,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_558])).

tff(c_46,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_499,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14,c_492])).

tff(c_5661,plain,(
    ! [A_191,B_192,C_193] : k5_xboole_0(k5_xboole_0(A_191,B_192),k5_xboole_0(k2_xboole_0(A_191,B_192),C_193)) = k5_xboole_0(k3_xboole_0(A_191,B_192),C_193) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_16])).

tff(c_5985,plain,(
    ! [A_191,B_192] : k5_xboole_0(k3_xboole_0(A_191,B_192),k2_xboole_0(A_191,B_192)) = k5_xboole_0(k5_xboole_0(A_191,B_192),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_5661])).

tff(c_6069,plain,(
    ! [A_194,B_195] : k5_xboole_0(k3_xboole_0(A_194,B_195),k2_xboole_0(A_194,B_195)) = k5_xboole_0(A_194,B_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5985])).

tff(c_6184,plain,(
    k5_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) = k5_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_6069])).

tff(c_6208,plain,(
    k5_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) = k5_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6184])).

tff(c_6276,plain,(
    k5_xboole_0(k2_tarski('#skF_1','#skF_2'),k5_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) = k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6208,c_538])).

tff(c_6293,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_6276])).

tff(c_39664,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_39528,c_6293])).

tff(c_2994,plain,(
    ! [A_149,B_150] : k5_xboole_0(k2_xboole_0(A_149,B_150),k5_xboole_0(A_149,B_150)) = k3_xboole_0(A_149,B_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_2])).

tff(c_3137,plain,(
    ! [A_1,B_2] : k5_xboole_0(k2_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2994])).

tff(c_41811,plain,(
    k5_xboole_0('#skF_3',k5_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) = k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_39664,c_3137])).

tff(c_41837,plain,(
    k3_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) = k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_2,c_41811])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47812,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_41837,c_8])).

tff(c_42,plain,(
    ! [A_48,C_50,B_49] :
      ( r2_hidden(A_48,C_50)
      | ~ r1_tarski(k2_tarski(A_48,B_49),C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_47833,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_47812,c_42])).

tff(c_47838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_47833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.06/13.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.06/13.86  
% 22.06/13.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.06/13.86  %$ r2_hidden > r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 22.06/13.86  
% 22.06/13.86  %Foreground sorts:
% 22.06/13.86  
% 22.06/13.86  
% 22.06/13.86  %Background operators:
% 22.06/13.86  
% 22.06/13.86  
% 22.06/13.86  %Foreground operators:
% 22.06/13.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.06/13.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.06/13.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.06/13.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.06/13.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 22.06/13.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 22.06/13.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.06/13.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 22.06/13.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.06/13.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 22.06/13.86  tff('#skF_2', type, '#skF_2': $i).
% 22.06/13.86  tff('#skF_3', type, '#skF_3': $i).
% 22.06/13.86  tff('#skF_1', type, '#skF_1': $i).
% 22.06/13.86  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.06/13.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.06/13.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 22.06/13.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.06/13.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.06/13.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.06/13.86  
% 22.06/13.88  tff(f_72, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 22.06/13.88  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 22.06/13.88  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 22.06/13.88  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 22.06/13.88  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 22.06/13.88  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 22.06/13.88  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 22.06/13.88  tff(f_47, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 22.06/13.88  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 22.06/13.88  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 22.06/13.88  tff(f_55, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 22.06/13.88  tff(f_57, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 22.06/13.88  tff(f_45, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 22.06/13.88  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 22.06/13.88  tff(f_59, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 22.06/13.88  tff(f_49, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 22.06/13.88  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 22.06/13.88  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 22.06/13.88  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 22.06/13.88  tff(c_44, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.06/13.88  tff(c_136, plain, (![B_61, A_62]: (k5_xboole_0(B_61, A_62)=k5_xboole_0(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.06/13.88  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 22.06/13.88  tff(c_152, plain, (![A_62]: (k5_xboole_0(k1_xboole_0, A_62)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_136, c_14])).
% 22.06/13.88  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.06/13.88  tff(c_10, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.06/13.88  tff(c_440, plain, (![A_93, B_94]: (k5_xboole_0(k5_xboole_0(A_93, B_94), k2_xboole_0(A_93, B_94))=k3_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_43])).
% 22.06/13.88  tff(c_492, plain, (![A_9]: (k5_xboole_0(k5_xboole_0(A_9, k1_xboole_0), A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_440])).
% 22.06/13.88  tff(c_501, plain, (![A_95]: (k5_xboole_0(A_95, A_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_492])).
% 22.06/13.88  tff(c_16, plain, (![A_12, B_13, C_14]: (k5_xboole_0(k5_xboole_0(A_12, B_13), C_14)=k5_xboole_0(A_12, k5_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 22.06/13.88  tff(c_509, plain, (![A_95, C_14]: (k5_xboole_0(A_95, k5_xboole_0(A_95, C_14))=k5_xboole_0(k1_xboole_0, C_14))), inference(superposition, [status(thm), theory('equality')], [c_501, c_16])).
% 22.06/13.88  tff(c_538, plain, (![A_95, C_14]: (k5_xboole_0(A_95, k5_xboole_0(A_95, C_14))=C_14)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_509])).
% 22.06/13.88  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.06/13.88  tff(c_254, plain, (![C_69, B_70, A_71]: (k1_enumset1(C_69, B_70, A_71)=k1_enumset1(A_71, B_70, C_69))), inference(cnfTransformation, [status(thm)], [f_47])).
% 22.06/13.88  tff(c_28, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.06/13.88  tff(c_270, plain, (![C_69, B_70]: (k1_enumset1(C_69, B_70, B_70)=k2_tarski(B_70, C_69))), inference(superposition, [status(thm), theory('equality')], [c_254, c_28])).
% 22.06/13.88  tff(c_26, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.06/13.88  tff(c_30, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 22.06/13.88  tff(c_32, plain, (![A_37, B_38, C_39, D_40]: (k3_enumset1(A_37, A_37, B_38, C_39, D_40)=k2_enumset1(A_37, B_38, C_39, D_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 22.06/13.88  tff(c_947, plain, (![B_118, A_117, D_119, C_116, E_120]: (k2_xboole_0(k1_enumset1(A_117, B_118, C_116), k2_tarski(D_119, E_120))=k3_enumset1(A_117, B_118, C_116, D_119, E_120))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.06/13.88  tff(c_968, plain, (![A_32, B_33, D_119, E_120]: (k3_enumset1(A_32, A_32, B_33, D_119, E_120)=k2_xboole_0(k2_tarski(A_32, B_33), k2_tarski(D_119, E_120)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_947])).
% 22.06/13.88  tff(c_4565, plain, (![A_163, B_164, D_165, E_166]: (k2_xboole_0(k2_tarski(A_163, B_164), k2_tarski(D_165, E_166))=k2_enumset1(A_163, B_164, D_165, E_166))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_968])).
% 22.06/13.88  tff(c_4596, plain, (![A_31, D_165, E_166]: (k2_xboole_0(k1_tarski(A_31), k2_tarski(D_165, E_166))=k2_enumset1(A_31, A_31, D_165, E_166))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4565])).
% 22.06/13.88  tff(c_5425, plain, (![A_173, D_174, E_175]: (k2_xboole_0(k1_tarski(A_173), k2_tarski(D_174, E_175))=k1_enumset1(A_173, D_174, E_175))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4596])).
% 22.06/13.88  tff(c_5452, plain, (![A_173, A_31]: (k2_xboole_0(k1_tarski(A_173), k1_tarski(A_31))=k1_enumset1(A_173, A_31, A_31))), inference(superposition, [status(thm), theory('equality')], [c_26, c_5425])).
% 22.06/13.88  tff(c_5455, plain, (![A_173, A_31]: (k2_xboole_0(k1_tarski(A_173), k1_tarski(A_31))=k2_tarski(A_31, A_173))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_5452])).
% 22.06/13.88  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.06/13.88  tff(c_4607, plain, (![D_167, E_168]: (k2_enumset1(D_167, E_168, D_167, E_168)=k2_tarski(D_167, E_168))), inference(superposition, [status(thm), theory('equality')], [c_4565, c_4])).
% 22.06/13.88  tff(c_4614, plain, (![E_168]: (k1_enumset1(E_168, E_168, E_168)=k2_tarski(E_168, E_168))), inference(superposition, [status(thm), theory('equality')], [c_4607, c_30])).
% 22.06/13.88  tff(c_4623, plain, (![E_168]: (k1_enumset1(E_168, E_168, E_168)=k1_tarski(E_168))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4614])).
% 22.06/13.88  tff(c_34, plain, (![D_44, C_43, A_41, B_42, E_45]: (k4_enumset1(A_41, A_41, B_42, C_43, D_44, E_45)=k3_enumset1(A_41, B_42, C_43, D_44, E_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.06/13.88  tff(c_1137, plain, (![C_126, F_127, E_129, D_124, A_125, B_128]: (k2_xboole_0(k3_enumset1(A_125, B_128, C_126, D_124, E_129), k1_tarski(F_127))=k4_enumset1(A_125, B_128, C_126, D_124, E_129, F_127))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.06/13.88  tff(c_1149, plain, (![C_39, B_38, F_127, A_37, D_40]: (k4_enumset1(A_37, A_37, B_38, C_39, D_40, F_127)=k2_xboole_0(k2_enumset1(A_37, B_38, C_39, D_40), k1_tarski(F_127)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1137])).
% 22.06/13.88  tff(c_5618, plain, (![D_188, F_190, A_186, C_189, B_187]: (k2_xboole_0(k2_enumset1(A_186, B_187, C_189, D_188), k1_tarski(F_190))=k3_enumset1(A_186, B_187, C_189, D_188, F_190))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1149])).
% 22.06/13.88  tff(c_5651, plain, (![A_34, B_35, C_36, F_190]: (k3_enumset1(A_34, A_34, B_35, C_36, F_190)=k2_xboole_0(k1_enumset1(A_34, B_35, C_36), k1_tarski(F_190)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_5618])).
% 22.06/13.88  tff(c_38419, plain, (![A_342, B_343, C_344, F_345]: (k2_xboole_0(k1_enumset1(A_342, B_343, C_344), k1_tarski(F_345))=k2_enumset1(A_342, B_343, C_344, F_345))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5651])).
% 22.06/13.88  tff(c_38488, plain, (![E_168, F_345]: (k2_xboole_0(k1_tarski(E_168), k1_tarski(F_345))=k2_enumset1(E_168, E_168, E_168, F_345))), inference(superposition, [status(thm), theory('equality')], [c_4623, c_38419])).
% 22.06/13.88  tff(c_38506, plain, (![E_346, F_347]: (k2_enumset1(E_346, E_346, E_346, F_347)=k2_tarski(F_347, E_346))), inference(demodulation, [status(thm), theory('equality')], [c_5455, c_38488])).
% 22.06/13.88  tff(c_38555, plain, (![E_348, F_349]: (k1_enumset1(E_348, E_348, F_349)=k2_tarski(F_349, E_348))), inference(superposition, [status(thm), theory('equality')], [c_38506, c_30])).
% 22.06/13.88  tff(c_38619, plain, (![F_350, E_351]: (k2_tarski(F_350, E_351)=k2_tarski(E_351, F_350))), inference(superposition, [status(thm), theory('equality')], [c_38555, c_28])).
% 22.06/13.88  tff(c_36, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.06/13.88  tff(c_39490, plain, (![F_359, E_360]: (k3_tarski(k2_tarski(F_359, E_360))=k2_xboole_0(E_360, F_359))), inference(superposition, [status(thm), theory('equality')], [c_38619, c_36])).
% 22.06/13.88  tff(c_39528, plain, (![F_361, E_362]: (k2_xboole_0(F_361, E_362)=k2_xboole_0(E_362, F_361))), inference(superposition, [status(thm), theory('equality')], [c_39490, c_36])).
% 22.06/13.88  tff(c_558, plain, (![A_99, C_100]: (k5_xboole_0(A_99, k5_xboole_0(A_99, C_100))=C_100)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_509])).
% 22.06/13.88  tff(c_607, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_558])).
% 22.06/13.88  tff(c_46, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 22.06/13.88  tff(c_499, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14, c_492])).
% 22.06/13.88  tff(c_5661, plain, (![A_191, B_192, C_193]: (k5_xboole_0(k5_xboole_0(A_191, B_192), k5_xboole_0(k2_xboole_0(A_191, B_192), C_193))=k5_xboole_0(k3_xboole_0(A_191, B_192), C_193))), inference(superposition, [status(thm), theory('equality')], [c_440, c_16])).
% 22.06/13.88  tff(c_5985, plain, (![A_191, B_192]: (k5_xboole_0(k3_xboole_0(A_191, B_192), k2_xboole_0(A_191, B_192))=k5_xboole_0(k5_xboole_0(A_191, B_192), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_499, c_5661])).
% 22.06/13.88  tff(c_6069, plain, (![A_194, B_195]: (k5_xboole_0(k3_xboole_0(A_194, B_195), k2_xboole_0(A_194, B_195))=k5_xboole_0(A_194, B_195))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5985])).
% 22.06/13.88  tff(c_6184, plain, (k5_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))=k5_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_46, c_6069])).
% 22.06/13.88  tff(c_6208, plain, (k5_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))=k5_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6184])).
% 22.06/13.88  tff(c_6276, plain, (k5_xboole_0(k2_tarski('#skF_1', '#skF_2'), k5_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))=k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6208, c_538])).
% 22.06/13.88  tff(c_6293, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_607, c_6276])).
% 22.06/13.88  tff(c_39664, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_39528, c_6293])).
% 22.06/13.88  tff(c_2994, plain, (![A_149, B_150]: (k5_xboole_0(k2_xboole_0(A_149, B_150), k5_xboole_0(A_149, B_150))=k3_xboole_0(A_149, B_150))), inference(superposition, [status(thm), theory('equality')], [c_440, c_2])).
% 22.06/13.88  tff(c_3137, plain, (![A_1, B_2]: (k5_xboole_0(k2_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1))=k3_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2994])).
% 22.06/13.88  tff(c_41811, plain, (k5_xboole_0('#skF_3', k5_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))=k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_39664, c_3137])).
% 22.06/13.88  tff(c_41837, plain, (k3_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_2, c_41811])).
% 22.06/13.88  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.06/13.88  tff(c_47812, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_41837, c_8])).
% 22.06/13.88  tff(c_42, plain, (![A_48, C_50, B_49]: (r2_hidden(A_48, C_50) | ~r1_tarski(k2_tarski(A_48, B_49), C_50))), inference(cnfTransformation, [status(thm)], [f_67])).
% 22.06/13.88  tff(c_47833, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_47812, c_42])).
% 22.06/13.88  tff(c_47838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_47833])).
% 22.06/13.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.06/13.88  
% 22.06/13.88  Inference rules
% 22.06/13.88  ----------------------
% 22.06/13.88  #Ref     : 0
% 22.06/13.88  #Sup     : 12655
% 22.06/13.88  #Fact    : 0
% 22.06/13.88  #Define  : 0
% 22.06/13.88  #Split   : 0
% 22.06/13.88  #Chain   : 0
% 22.06/13.88  #Close   : 0
% 22.06/13.88  
% 22.06/13.88  Ordering : KBO
% 22.06/13.88  
% 22.06/13.88  Simplification rules
% 22.06/13.88  ----------------------
% 22.06/13.88  #Subsume      : 830
% 22.06/13.88  #Demod        : 18682
% 22.06/13.88  #Tautology    : 3913
% 22.06/13.88  #SimpNegUnit  : 1
% 22.06/13.88  #BackRed      : 20
% 22.06/13.88  
% 22.06/13.88  #Partial instantiations: 0
% 22.06/13.88  #Strategies tried      : 1
% 22.06/13.88  
% 22.06/13.88  Timing (in seconds)
% 22.06/13.88  ----------------------
% 22.06/13.89  Preprocessing        : 0.29
% 22.06/13.89  Parsing              : 0.16
% 22.06/13.89  CNF conversion       : 0.02
% 22.06/13.89  Main loop            : 12.86
% 22.06/13.89  Inferencing          : 1.27
% 22.06/13.89  Reduction            : 9.72
% 22.06/13.89  Demodulation         : 9.32
% 22.06/13.89  BG Simplification    : 0.24
% 22.06/13.89  Subsumption          : 1.34
% 22.06/13.89  Abstraction          : 0.40
% 22.06/13.89  MUC search           : 0.00
% 22.06/13.89  Cooper               : 0.00
% 22.06/13.89  Total                : 13.19
% 22.06/13.89  Index Insertion      : 0.00
% 22.06/13.89  Index Deletion       : 0.00
% 22.06/13.89  Index Matching       : 0.00
% 22.06/13.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
