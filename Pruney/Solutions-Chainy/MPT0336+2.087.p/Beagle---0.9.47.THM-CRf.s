%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:12 EST 2020

% Result     : Theorem 22.05s
% Output     : CNFRefutation 22.05s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 241 expanded)
%              Number of leaves         :   28 (  92 expanded)
%              Depth                    :   17
%              Number of atoms          :  134 ( 429 expanded)
%              Number of equality atoms :   33 (  90 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_108,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k4_xboole_0(A_40,B_41) != A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [B_41,A_40] :
      ( r1_xboole_0(B_41,A_40)
      | k4_xboole_0(A_40,B_41) != A_40 ) ),
    inference(resolution,[status(thm)],[c_108,c_4])).

tff(c_42,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_59,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(B_34,A_35)
      | ~ r1_xboole_0(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_1438,plain,(
    ! [A_128,C_129,B_130] :
      ( ~ r1_xboole_0(A_128,C_129)
      | ~ r1_xboole_0(A_128,B_130)
      | r1_xboole_0(A_128,k2_xboole_0(B_130,C_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5138,plain,(
    ! [B_248,C_249,A_250] :
      ( r1_xboole_0(k2_xboole_0(B_248,C_249),A_250)
      | ~ r1_xboole_0(A_250,C_249)
      | ~ r1_xboole_0(A_250,B_248) ) ),
    inference(resolution,[status(thm)],[c_1438,c_4])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5156,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_5138,c_40])).

tff(c_5164,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_5156])).

tff(c_5175,plain,(
    k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_114,c_5164])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_47,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_116,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = A_42
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_134,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_65,c_116])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5160,plain,(
    ! [B_248,C_249,A_250] :
      ( k4_xboole_0(k2_xboole_0(B_248,C_249),A_250) = k2_xboole_0(B_248,C_249)
      | ~ r1_xboole_0(A_250,C_249)
      | ~ r1_xboole_0(A_250,B_248) ) ),
    inference(resolution,[status(thm)],[c_5138,c_28])).

tff(c_38,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,k1_tarski(B_28)) = A_27
      | r2_hidden(B_28,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_256,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_xboole_0(A_62,C_63)
      | ~ r1_xboole_0(A_62,k2_xboole_0(B_64,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22222,plain,(
    ! [B_616,C_617,B_618] :
      ( r1_xboole_0(B_616,C_617)
      | k4_xboole_0(k2_xboole_0(B_618,C_617),B_616) != k2_xboole_0(B_618,C_617) ) ),
    inference(resolution,[status(thm)],[c_114,c_256])).

tff(c_70884,plain,(
    ! [B_1071,C_1072,B_1073] :
      ( r1_xboole_0(k1_tarski(B_1071),C_1072)
      | r2_hidden(B_1071,k2_xboole_0(B_1073,C_1072)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_22222])).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1180,plain,(
    ! [A_118,B_119,C_120] :
      ( ~ r1_xboole_0(A_118,B_119)
      | ~ r2_hidden(C_120,B_119)
      | ~ r2_hidden(C_120,A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4222,plain,(
    ! [C_217,B_218,A_219] :
      ( ~ r2_hidden(C_217,B_218)
      | ~ r2_hidden(C_217,A_219)
      | k4_xboole_0(A_219,B_218) != A_219 ) ),
    inference(resolution,[status(thm)],[c_30,c_1180])).

tff(c_4231,plain,(
    ! [A_219] :
      ( ~ r2_hidden('#skF_5',A_219)
      | k4_xboole_0(A_219,'#skF_4') != A_219 ) ),
    inference(resolution,[status(thm)],[c_44,c_4222])).

tff(c_71085,plain,(
    ! [B_1080,C_1081] :
      ( k4_xboole_0(k2_xboole_0(B_1080,C_1081),'#skF_4') != k2_xboole_0(B_1080,C_1081)
      | r1_xboole_0(k1_tarski('#skF_5'),C_1081) ) ),
    inference(resolution,[status(thm)],[c_70884,c_4231])).

tff(c_71095,plain,(
    ! [C_249,B_248] :
      ( r1_xboole_0(k1_tarski('#skF_5'),C_249)
      | ~ r1_xboole_0('#skF_4',C_249)
      | ~ r1_xboole_0('#skF_4',B_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5160,c_71085])).

tff(c_71850,plain,(
    ! [B_248] : ~ r1_xboole_0('#skF_4',B_248) ),
    inference(splitLeft,[status(thm)],[c_71095])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_912,plain,(
    ! [A_105,C_106,B_107] :
      ( r1_xboole_0(A_105,C_106)
      | ~ r1_tarski(A_105,k4_xboole_0(B_107,C_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1027,plain,(
    ! [B_112,C_113,B_114] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_112,C_113),B_114),C_113) ),
    inference(resolution,[status(thm)],[c_16,c_912])).

tff(c_1117,plain,(
    ! [B_116] : r1_xboole_0(k4_xboole_0('#skF_3',B_116),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_1027])).

tff(c_1351,plain,(
    ! [B_125] : r1_xboole_0('#skF_4',k4_xboole_0('#skF_3',B_125)) ),
    inference(resolution,[status(thm)],[c_1117,c_4])).

tff(c_1378,plain,(
    ! [B_125] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_3',B_125)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1351,c_28])).

tff(c_26,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_64,plain,(
    ! [B_21,A_20] : r1_xboole_0(B_21,k4_xboole_0(A_20,B_21)) ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_133,plain,(
    ! [B_21,A_20] : k4_xboole_0(B_21,k4_xboole_0(A_20,B_21)) = B_21 ),
    inference(resolution,[status(thm)],[c_64,c_116])).

tff(c_348,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_380,plain,(
    ! [A_77,B_78] : r1_tarski(k3_xboole_0(A_77,B_78),A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_16])).

tff(c_2524,plain,(
    ! [B_162,C_163,B_164] : r1_xboole_0(k3_xboole_0(k4_xboole_0(B_162,C_163),B_164),C_163) ),
    inference(resolution,[status(thm)],[c_380,c_912])).

tff(c_3679,plain,(
    ! [B_205,B_206,A_207] : r1_xboole_0(k3_xboole_0(B_205,B_206),k4_xboole_0(A_207,B_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_2524])).

tff(c_4493,plain,(
    ! [A_230,B_231,B_232] : r1_xboole_0(k4_xboole_0(A_230,B_231),k3_xboole_0(B_231,B_232)) ),
    inference(resolution,[status(thm)],[c_3679,c_4])).

tff(c_6070,plain,(
    ! [A_276,B_277,A_278] : r1_xboole_0(k4_xboole_0(A_276,B_277),k3_xboole_0(A_278,B_277)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4493])).

tff(c_8419,plain,(
    ! [A_349,B_350] : r1_xboole_0('#skF_4',k3_xboole_0(A_349,k4_xboole_0('#skF_3',B_350))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1378,c_6070])).

tff(c_10559,plain,(
    ! [A_435,B_436] : r1_xboole_0('#skF_4',k3_xboole_0(A_435,k3_xboole_0('#skF_3',B_436))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_8419])).

tff(c_10582,plain,(
    ! [A_435,B_2] : r1_xboole_0('#skF_4',k3_xboole_0(A_435,k3_xboole_0(B_2,'#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10559])).

tff(c_71870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71850,c_10582])).

tff(c_71872,plain,(
    ! [C_1096] :
      ( r1_xboole_0(k1_tarski('#skF_5'),C_1096)
      | ~ r1_xboole_0('#skF_4',C_1096) ) ),
    inference(splitRight,[status(thm)],[c_71095])).

tff(c_71893,plain,(
    ! [C_1097] :
      ( r1_xboole_0(C_1097,k1_tarski('#skF_5'))
      | ~ r1_xboole_0('#skF_4',C_1097) ) ),
    inference(resolution,[status(thm)],[c_71872,c_4])).

tff(c_75544,plain,(
    ! [C_1152] :
      ( k4_xboole_0(C_1152,k1_tarski('#skF_5')) = C_1152
      | ~ r1_xboole_0('#skF_4',C_1152) ) ),
    inference(resolution,[status(thm)],[c_71893,c_28])).

tff(c_24770,plain,(
    ! [B_683,C_684,B_685] : k4_xboole_0(k4_xboole_0(k4_xboole_0(B_683,C_684),B_685),C_684) = k4_xboole_0(k4_xboole_0(B_683,C_684),B_685) ),
    inference(resolution,[status(thm)],[c_1027,c_28])).

tff(c_25239,plain,(
    ! [B_685] : k4_xboole_0(k4_xboole_0('#skF_3',B_685),'#skF_4') = k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),B_685) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_24770])).

tff(c_25347,plain,(
    ! [B_685] : k4_xboole_0(k4_xboole_0('#skF_3',B_685),'#skF_4') = k4_xboole_0('#skF_3',B_685) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_25239])).

tff(c_75774,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_5')) = k4_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_75544,c_25347])).

tff(c_76312,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_134,c_75774])).

tff(c_15812,plain,(
    ! [A_542,A_543,B_544] :
      ( r1_xboole_0(A_542,k4_xboole_0(A_543,B_544))
      | ~ r1_tarski(A_542,B_544) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_912])).

tff(c_15900,plain,(
    ! [A_543,B_544,A_542] :
      ( r1_xboole_0(k4_xboole_0(A_543,B_544),A_542)
      | ~ r1_tarski(A_542,B_544) ) ),
    inference(resolution,[status(thm)],[c_15812,c_4])).

tff(c_79789,plain,(
    ! [A_1203] :
      ( r1_xboole_0('#skF_3',A_1203)
      | ~ r1_tarski(A_1203,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76312,c_15900])).

tff(c_79891,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_47,c_79789])).

tff(c_79902,plain,(
    k4_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_79891,c_28])).

tff(c_351,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,k4_xboole_0(A_77,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_18])).

tff(c_80532,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_79902,c_351])).

tff(c_3328,plain,(
    ! [C_197,B_198,B_199] : r1_xboole_0(C_197,k3_xboole_0(k4_xboole_0(B_198,C_197),B_199)) ),
    inference(resolution,[status(thm)],[c_2524,c_4])).

tff(c_4239,plain,(
    ! [C_221,A_222,B_223] : r1_xboole_0(C_221,k3_xboole_0(A_222,k4_xboole_0(B_223,C_221))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3328])).

tff(c_4308,plain,(
    ! [C_221,A_222,B_223] : k4_xboole_0(C_221,k3_xboole_0(A_222,k4_xboole_0(B_223,C_221))) = C_221 ),
    inference(resolution,[status(thm)],[c_4239,c_28])).

tff(c_80721,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_80532,c_4308])).

tff(c_80921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5175,c_80721])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:41:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.05/12.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.05/12.86  
% 22.05/12.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.05/12.86  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 22.05/12.86  
% 22.05/12.86  %Foreground sorts:
% 22.05/12.86  
% 22.05/12.86  
% 22.05/12.86  %Background operators:
% 22.05/12.86  
% 22.05/12.86  
% 22.05/12.86  %Foreground operators:
% 22.05/12.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.05/12.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.05/12.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.05/12.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 22.05/12.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.05/12.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 22.05/12.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 22.05/12.86  tff('#skF_5', type, '#skF_5': $i).
% 22.05/12.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 22.05/12.86  tff('#skF_2', type, '#skF_2': $i).
% 22.05/12.86  tff('#skF_3', type, '#skF_3': $i).
% 22.05/12.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.05/12.86  tff('#skF_4', type, '#skF_4': $i).
% 22.05/12.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.05/12.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 22.05/12.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.05/12.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.05/12.86  
% 22.05/12.88  tff(f_81, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 22.05/12.88  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 22.05/12.88  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 22.05/12.88  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 22.05/12.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 22.05/12.88  tff(f_90, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 22.05/12.88  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 22.05/12.88  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 22.05/12.88  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 22.05/12.88  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 22.05/12.88  tff(f_77, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 22.05/12.88  tff(c_108, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k4_xboole_0(A_40, B_41)!=A_40)), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.05/12.88  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.05/12.88  tff(c_114, plain, (![B_41, A_40]: (r1_xboole_0(B_41, A_40) | k4_xboole_0(A_40, B_41)!=A_40)), inference(resolution, [status(thm)], [c_108, c_4])).
% 22.05/12.88  tff(c_42, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.05/12.88  tff(c_59, plain, (![B_34, A_35]: (r1_xboole_0(B_34, A_35) | ~r1_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.05/12.88  tff(c_65, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_59])).
% 22.05/12.88  tff(c_1438, plain, (![A_128, C_129, B_130]: (~r1_xboole_0(A_128, C_129) | ~r1_xboole_0(A_128, B_130) | r1_xboole_0(A_128, k2_xboole_0(B_130, C_129)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 22.05/12.88  tff(c_5138, plain, (![B_248, C_249, A_250]: (r1_xboole_0(k2_xboole_0(B_248, C_249), A_250) | ~r1_xboole_0(A_250, C_249) | ~r1_xboole_0(A_250, B_248))), inference(resolution, [status(thm)], [c_1438, c_4])).
% 22.05/12.88  tff(c_40, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.05/12.88  tff(c_5156, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_5138, c_40])).
% 22.05/12.88  tff(c_5164, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_5156])).
% 22.05/12.88  tff(c_5175, plain, (k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_114, c_5164])).
% 22.05/12.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.05/12.88  tff(c_46, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.05/12.88  tff(c_47, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 22.05/12.88  tff(c_116, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=A_42 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.05/12.88  tff(c_134, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_65, c_116])).
% 22.05/12.88  tff(c_28, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.05/12.88  tff(c_5160, plain, (![B_248, C_249, A_250]: (k4_xboole_0(k2_xboole_0(B_248, C_249), A_250)=k2_xboole_0(B_248, C_249) | ~r1_xboole_0(A_250, C_249) | ~r1_xboole_0(A_250, B_248))), inference(resolution, [status(thm)], [c_5138, c_28])).
% 22.05/12.88  tff(c_38, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k1_tarski(B_28))=A_27 | r2_hidden(B_28, A_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 22.05/12.88  tff(c_256, plain, (![A_62, C_63, B_64]: (r1_xboole_0(A_62, C_63) | ~r1_xboole_0(A_62, k2_xboole_0(B_64, C_63)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 22.05/12.88  tff(c_22222, plain, (![B_616, C_617, B_618]: (r1_xboole_0(B_616, C_617) | k4_xboole_0(k2_xboole_0(B_618, C_617), B_616)!=k2_xboole_0(B_618, C_617))), inference(resolution, [status(thm)], [c_114, c_256])).
% 22.05/12.88  tff(c_70884, plain, (![B_1071, C_1072, B_1073]: (r1_xboole_0(k1_tarski(B_1071), C_1072) | r2_hidden(B_1071, k2_xboole_0(B_1073, C_1072)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_22222])).
% 22.05/12.88  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 22.05/12.88  tff(c_30, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k4_xboole_0(A_22, B_23)!=A_22)), inference(cnfTransformation, [status(thm)], [f_81])).
% 22.05/12.88  tff(c_1180, plain, (![A_118, B_119, C_120]: (~r1_xboole_0(A_118, B_119) | ~r2_hidden(C_120, B_119) | ~r2_hidden(C_120, A_118))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.05/12.88  tff(c_4222, plain, (![C_217, B_218, A_219]: (~r2_hidden(C_217, B_218) | ~r2_hidden(C_217, A_219) | k4_xboole_0(A_219, B_218)!=A_219)), inference(resolution, [status(thm)], [c_30, c_1180])).
% 22.05/12.88  tff(c_4231, plain, (![A_219]: (~r2_hidden('#skF_5', A_219) | k4_xboole_0(A_219, '#skF_4')!=A_219)), inference(resolution, [status(thm)], [c_44, c_4222])).
% 22.05/12.88  tff(c_71085, plain, (![B_1080, C_1081]: (k4_xboole_0(k2_xboole_0(B_1080, C_1081), '#skF_4')!=k2_xboole_0(B_1080, C_1081) | r1_xboole_0(k1_tarski('#skF_5'), C_1081))), inference(resolution, [status(thm)], [c_70884, c_4231])).
% 22.05/12.88  tff(c_71095, plain, (![C_249, B_248]: (r1_xboole_0(k1_tarski('#skF_5'), C_249) | ~r1_xboole_0('#skF_4', C_249) | ~r1_xboole_0('#skF_4', B_248))), inference(superposition, [status(thm), theory('equality')], [c_5160, c_71085])).
% 22.05/12.88  tff(c_71850, plain, (![B_248]: (~r1_xboole_0('#skF_4', B_248))), inference(splitLeft, [status(thm)], [c_71095])).
% 22.05/12.88  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.05/12.88  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 22.05/12.88  tff(c_912, plain, (![A_105, C_106, B_107]: (r1_xboole_0(A_105, C_106) | ~r1_tarski(A_105, k4_xboole_0(B_107, C_106)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 22.05/12.88  tff(c_1027, plain, (![B_112, C_113, B_114]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_112, C_113), B_114), C_113))), inference(resolution, [status(thm)], [c_16, c_912])).
% 22.05/12.88  tff(c_1117, plain, (![B_116]: (r1_xboole_0(k4_xboole_0('#skF_3', B_116), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_1027])).
% 22.05/12.88  tff(c_1351, plain, (![B_125]: (r1_xboole_0('#skF_4', k4_xboole_0('#skF_3', B_125)))), inference(resolution, [status(thm)], [c_1117, c_4])).
% 22.05/12.88  tff(c_1378, plain, (![B_125]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_3', B_125))='#skF_4')), inference(resolution, [status(thm)], [c_1351, c_28])).
% 22.05/12.88  tff(c_26, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 22.05/12.88  tff(c_64, plain, (![B_21, A_20]: (r1_xboole_0(B_21, k4_xboole_0(A_20, B_21)))), inference(resolution, [status(thm)], [c_26, c_59])).
% 22.05/12.88  tff(c_133, plain, (![B_21, A_20]: (k4_xboole_0(B_21, k4_xboole_0(A_20, B_21))=B_21)), inference(resolution, [status(thm)], [c_64, c_116])).
% 22.05/12.88  tff(c_348, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.05/12.88  tff(c_380, plain, (![A_77, B_78]: (r1_tarski(k3_xboole_0(A_77, B_78), A_77))), inference(superposition, [status(thm), theory('equality')], [c_348, c_16])).
% 22.05/12.88  tff(c_2524, plain, (![B_162, C_163, B_164]: (r1_xboole_0(k3_xboole_0(k4_xboole_0(B_162, C_163), B_164), C_163))), inference(resolution, [status(thm)], [c_380, c_912])).
% 22.05/12.88  tff(c_3679, plain, (![B_205, B_206, A_207]: (r1_xboole_0(k3_xboole_0(B_205, B_206), k4_xboole_0(A_207, B_205)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_2524])).
% 22.05/12.88  tff(c_4493, plain, (![A_230, B_231, B_232]: (r1_xboole_0(k4_xboole_0(A_230, B_231), k3_xboole_0(B_231, B_232)))), inference(resolution, [status(thm)], [c_3679, c_4])).
% 22.05/12.88  tff(c_6070, plain, (![A_276, B_277, A_278]: (r1_xboole_0(k4_xboole_0(A_276, B_277), k3_xboole_0(A_278, B_277)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4493])).
% 22.05/12.88  tff(c_8419, plain, (![A_349, B_350]: (r1_xboole_0('#skF_4', k3_xboole_0(A_349, k4_xboole_0('#skF_3', B_350))))), inference(superposition, [status(thm), theory('equality')], [c_1378, c_6070])).
% 22.05/12.88  tff(c_10559, plain, (![A_435, B_436]: (r1_xboole_0('#skF_4', k3_xboole_0(A_435, k3_xboole_0('#skF_3', B_436))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_8419])).
% 22.05/12.88  tff(c_10582, plain, (![A_435, B_2]: (r1_xboole_0('#skF_4', k3_xboole_0(A_435, k3_xboole_0(B_2, '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10559])).
% 22.05/12.88  tff(c_71870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71850, c_10582])).
% 22.05/12.88  tff(c_71872, plain, (![C_1096]: (r1_xboole_0(k1_tarski('#skF_5'), C_1096) | ~r1_xboole_0('#skF_4', C_1096))), inference(splitRight, [status(thm)], [c_71095])).
% 22.05/12.88  tff(c_71893, plain, (![C_1097]: (r1_xboole_0(C_1097, k1_tarski('#skF_5')) | ~r1_xboole_0('#skF_4', C_1097))), inference(resolution, [status(thm)], [c_71872, c_4])).
% 22.05/12.88  tff(c_75544, plain, (![C_1152]: (k4_xboole_0(C_1152, k1_tarski('#skF_5'))=C_1152 | ~r1_xboole_0('#skF_4', C_1152))), inference(resolution, [status(thm)], [c_71893, c_28])).
% 22.05/12.88  tff(c_24770, plain, (![B_683, C_684, B_685]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(B_683, C_684), B_685), C_684)=k4_xboole_0(k4_xboole_0(B_683, C_684), B_685))), inference(resolution, [status(thm)], [c_1027, c_28])).
% 22.05/12.88  tff(c_25239, plain, (![B_685]: (k4_xboole_0(k4_xboole_0('#skF_3', B_685), '#skF_4')=k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), B_685))), inference(superposition, [status(thm), theory('equality')], [c_134, c_24770])).
% 22.05/12.88  tff(c_25347, plain, (![B_685]: (k4_xboole_0(k4_xboole_0('#skF_3', B_685), '#skF_4')=k4_xboole_0('#skF_3', B_685))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_25239])).
% 22.05/12.88  tff(c_75774, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_5'))=k4_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_75544, c_25347])).
% 22.05/12.88  tff(c_76312, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_134, c_75774])).
% 22.05/12.88  tff(c_15812, plain, (![A_542, A_543, B_544]: (r1_xboole_0(A_542, k4_xboole_0(A_543, B_544)) | ~r1_tarski(A_542, B_544))), inference(superposition, [status(thm), theory('equality')], [c_133, c_912])).
% 22.05/12.88  tff(c_15900, plain, (![A_543, B_544, A_542]: (r1_xboole_0(k4_xboole_0(A_543, B_544), A_542) | ~r1_tarski(A_542, B_544))), inference(resolution, [status(thm)], [c_15812, c_4])).
% 22.05/12.88  tff(c_79789, plain, (![A_1203]: (r1_xboole_0('#skF_3', A_1203) | ~r1_tarski(A_1203, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_76312, c_15900])).
% 22.05/12.88  tff(c_79891, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_47, c_79789])).
% 22.05/12.88  tff(c_79902, plain, (k4_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_79891, c_28])).
% 22.05/12.88  tff(c_351, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k3_xboole_0(A_77, k4_xboole_0(A_77, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_348, c_18])).
% 22.05/12.88  tff(c_80532, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_79902, c_351])).
% 22.05/12.88  tff(c_3328, plain, (![C_197, B_198, B_199]: (r1_xboole_0(C_197, k3_xboole_0(k4_xboole_0(B_198, C_197), B_199)))), inference(resolution, [status(thm)], [c_2524, c_4])).
% 22.05/12.88  tff(c_4239, plain, (![C_221, A_222, B_223]: (r1_xboole_0(C_221, k3_xboole_0(A_222, k4_xboole_0(B_223, C_221))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3328])).
% 22.05/12.88  tff(c_4308, plain, (![C_221, A_222, B_223]: (k4_xboole_0(C_221, k3_xboole_0(A_222, k4_xboole_0(B_223, C_221)))=C_221)), inference(resolution, [status(thm)], [c_4239, c_28])).
% 22.05/12.88  tff(c_80721, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_80532, c_4308])).
% 22.05/12.88  tff(c_80921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5175, c_80721])).
% 22.05/12.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.05/12.88  
% 22.05/12.88  Inference rules
% 22.05/12.88  ----------------------
% 22.05/12.88  #Ref     : 1
% 22.05/12.88  #Sup     : 20036
% 22.05/12.88  #Fact    : 0
% 22.05/12.88  #Define  : 0
% 22.05/12.88  #Split   : 7
% 22.05/12.88  #Chain   : 0
% 22.05/12.88  #Close   : 0
% 22.05/12.88  
% 22.05/12.88  Ordering : KBO
% 22.05/12.88  
% 22.05/12.88  Simplification rules
% 22.05/12.88  ----------------------
% 22.05/12.88  #Subsume      : 2225
% 22.05/12.88  #Demod        : 14557
% 22.05/12.88  #Tautology    : 11437
% 22.05/12.88  #SimpNegUnit  : 170
% 22.05/12.88  #BackRed      : 94
% 22.05/12.88  
% 22.05/12.88  #Partial instantiations: 0
% 22.05/12.88  #Strategies tried      : 1
% 22.05/12.88  
% 22.05/12.88  Timing (in seconds)
% 22.05/12.88  ----------------------
% 22.05/12.88  Preprocessing        : 0.43
% 22.05/12.88  Parsing              : 0.19
% 22.05/12.88  CNF conversion       : 0.04
% 22.05/12.88  Main loop            : 11.68
% 22.05/12.88  Inferencing          : 1.47
% 22.05/12.88  Reduction            : 6.66
% 22.05/12.88  Demodulation         : 5.82
% 22.05/12.88  BG Simplification    : 0.16
% 22.05/12.88  Subsumption          : 2.76
% 22.05/12.88  Abstraction          : 0.21
% 22.05/12.88  MUC search           : 0.00
% 22.05/12.88  Cooper               : 0.00
% 22.05/12.88  Total                : 12.15
% 22.05/12.88  Index Insertion      : 0.00
% 22.05/12.88  Index Deletion       : 0.00
% 22.05/12.88  Index Matching       : 0.00
% 22.05/12.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
