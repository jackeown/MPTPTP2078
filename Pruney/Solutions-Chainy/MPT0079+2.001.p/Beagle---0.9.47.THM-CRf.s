%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:42 EST 2020

% Result     : Theorem 18.02s
% Output     : CNFRefutation 18.02s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 490 expanded)
%              Number of leaves         :   28 ( 174 expanded)
%              Depth                    :   22
%              Number of atoms          :  121 ( 559 expanded)
%              Number of equality atoms :   74 ( 424 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(c_34,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k2_xboole_0(A_42,B_43)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_89])).

tff(c_397,plain,(
    ! [A_61,B_62] : k2_xboole_0(A_61,k4_xboole_0(B_62,A_61)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_437,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = k2_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_397])).

tff(c_454,plain,(
    ! [A_63] : k2_xboole_0(A_63,k1_xboole_0) = A_63 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_437])).

tff(c_473,plain,(
    ! [A_63] : k2_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_2])).

tff(c_554,plain,(
    ! [A_66] : k2_xboole_0(k1_xboole_0,A_66) = A_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_2])).

tff(c_18,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_565,plain,(
    ! [B_18] : k4_xboole_0(B_18,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_18])).

tff(c_616,plain,(
    ! [B_18] : k4_xboole_0(B_18,k1_xboole_0) = B_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_565])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_277,plain,(
    ! [A_57,B_58,C_59] : r1_tarski(k3_xboole_0(A_57,B_58),k2_xboole_0(A_57,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_949,plain,(
    ! [A_78,B_79] : r1_tarski(k3_xboole_0(A_78,B_79),A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_277])).

tff(c_970,plain,(
    ! [B_4,A_3] : r1_tarski(k3_xboole_0(B_4,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_949])).

tff(c_307,plain,(
    ! [A_7,B_58] : r1_tarski(k3_xboole_0(A_7,B_58),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_277])).

tff(c_36,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1020,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_xboole_0 = A_82
      | ~ r1_xboole_0(B_83,C_84)
      | ~ r1_tarski(A_82,C_84)
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1255,plain,(
    ! [A_90] :
      ( k1_xboole_0 = A_90
      | ~ r1_tarski(A_90,'#skF_2')
      | ~ r1_tarski(A_90,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_1020])).

tff(c_2665,plain,(
    ! [B_121] :
      ( k3_xboole_0('#skF_2',B_121) = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_121),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_307,c_1255])).

tff(c_2687,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_970,c_2665])).

tff(c_24,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k3_xboole_0(A_24,B_25)) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2734,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2687,c_24])).

tff(c_2767,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_2734])).

tff(c_40,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_41,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_116,plain,(
    ! [B_45,A_46] : k2_xboole_0(B_45,A_46) = k2_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_34,B_35] : r1_tarski(A_34,k2_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_161,plain,(
    ! [A_47,B_48] : r1_tarski(A_47,k2_xboole_0(B_48,A_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_32])).

tff(c_170,plain,(
    r1_tarski('#skF_2',k2_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_161])).

tff(c_899,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_tarski(k4_xboole_0(A_75,B_76),C_77)
      | ~ r1_tarski(A_75,k2_xboole_0(B_76,C_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13372,plain,(
    ! [A_257,B_258,C_259] :
      ( k2_xboole_0(k4_xboole_0(A_257,B_258),C_259) = C_259
      | ~ r1_tarski(A_257,k2_xboole_0(B_258,C_259)) ) ),
    inference(resolution,[status(thm)],[c_899,c_12])).

tff(c_13542,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_4'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_170,c_13372])).

tff(c_13621,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2767,c_13542])).

tff(c_137,plain,(
    ! [A_46,B_45] : r1_tarski(A_46,k2_xboole_0(B_45,A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_32])).

tff(c_13693,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13621,c_137])).

tff(c_13723,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13693,c_12])).

tff(c_51,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_51])).

tff(c_44792,plain,(
    ! [B_426,C_427] : k2_xboole_0(k4_xboole_0(k2_xboole_0(B_426,C_427),B_426),C_427) = C_427 ),
    inference(resolution,[status(thm)],[c_54,c_13372])).

tff(c_45098,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1'),'#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_44792])).

tff(c_22,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_634,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k4_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_675,plain,(
    ! [A_22,B_23] : k3_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k4_xboole_0(A_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_634])).

tff(c_4758,plain,(
    ! [A_150,B_151] : k3_xboole_0(A_150,k2_xboole_0(A_150,B_151)) = A_150 ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_675])).

tff(c_4901,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4758])).

tff(c_134,plain,(
    ! [B_45,A_46] : k4_xboole_0(B_45,k2_xboole_0(A_46,B_45)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_22])).

tff(c_13690,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13621,c_134])).

tff(c_26,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_13790,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13690,c_26])).

tff(c_13819,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_4,c_13790])).

tff(c_1081,plain,(
    ! [A_86,B_87] : k2_xboole_0(k3_xboole_0(A_86,B_87),A_86) = A_86 ),
    inference(resolution,[status(thm)],[c_949,c_12])).

tff(c_1100,plain,(
    ! [A_86,B_87] : k2_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = A_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_2])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_240,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_252,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_240])).

tff(c_260,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_4])).

tff(c_804,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_833,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_804])).

tff(c_854,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_833])).

tff(c_1722,plain,(
    ! [A_103,B_104,C_105] : k2_xboole_0(k4_xboole_0(A_103,B_104),k3_xboole_0(A_103,C_105)) = k4_xboole_0(A_103,k4_xboole_0(B_104,C_105)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1778,plain,(
    ! [C_105] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_105)) = k2_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_1722])).

tff(c_1972,plain,(
    ! [C_110] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_3',C_110)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_1778])).

tff(c_2002,plain,(
    ! [B_27] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_3',B_27)) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1972])).

tff(c_14040,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_13819,c_2002])).

tff(c_18534,plain,(
    ! [A_294,B_295,B_296] : k2_xboole_0(k4_xboole_0(A_294,B_295),k3_xboole_0(B_296,A_294)) = k4_xboole_0(A_294,k4_xboole_0(B_295,B_296)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1722])).

tff(c_50964,plain,(
    ! [B_459,A_460,B_461] : r1_tarski(k3_xboole_0(B_459,A_460),k4_xboole_0(A_460,k4_xboole_0(B_461,B_459))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18534,c_137])).

tff(c_62985,plain,(
    ! [A_554] : r1_tarski(k3_xboole_0('#skF_2',A_554),k4_xboole_0(A_554,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14040,c_50964])).

tff(c_67480,plain,(
    ! [B_585] : r1_tarski('#skF_2',k4_xboole_0(k2_xboole_0(B_585,'#skF_2'),'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4901,c_62985])).

tff(c_67548,plain,(
    r1_tarski('#skF_2',k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_67480])).

tff(c_13567,plain,(
    ! [A_257,A_7] :
      ( k2_xboole_0(k4_xboole_0(A_257,A_7),A_7) = A_7
      | ~ r1_tarski(A_257,A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_13372])).

tff(c_13629,plain,(
    ! [A_7,A_257] :
      ( k2_xboole_0(A_7,A_257) = A_7
      | ~ r1_tarski(A_257,A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2,c_13567])).

tff(c_67580,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1'),'#skF_2') = k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_67548,c_13629])).

tff(c_67590,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45098,c_67580])).

tff(c_47435,plain,(
    ! [A_439,C_440,B_441] : r1_tarski(k3_xboole_0(A_439,C_440),k4_xboole_0(A_439,k4_xboole_0(B_441,C_440))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1722,c_137])).

tff(c_48944,plain,(
    ! [A_446] : r1_tarski(k3_xboole_0(A_446,'#skF_3'),k4_xboole_0(A_446,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_47435])).

tff(c_50655,plain,(
    ! [A_456] : r1_tarski(k3_xboole_0('#skF_3',A_456),k4_xboole_0(A_456,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_48944])).

tff(c_50696,plain,(
    ! [B_2] : r1_tarski('#skF_3',k4_xboole_0(k2_xboole_0(B_2,'#skF_3'),'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4901,c_50655])).

tff(c_67614,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_67590,c_50696])).

tff(c_67781,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_67614,c_13629])).

tff(c_67794,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13723,c_67781])).

tff(c_67796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_67794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:12:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.02/10.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.02/10.56  
% 18.02/10.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.02/10.56  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 18.02/10.56  
% 18.02/10.56  %Foreground sorts:
% 18.02/10.56  
% 18.02/10.56  
% 18.02/10.56  %Background operators:
% 18.02/10.56  
% 18.02/10.56  
% 18.02/10.56  %Foreground operators:
% 18.02/10.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.02/10.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.02/10.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.02/10.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.02/10.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 18.02/10.56  tff('#skF_2', type, '#skF_2': $i).
% 18.02/10.56  tff('#skF_3', type, '#skF_3': $i).
% 18.02/10.56  tff('#skF_1', type, '#skF_1': $i).
% 18.02/10.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.02/10.56  tff('#skF_4', type, '#skF_4': $i).
% 18.02/10.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.02/10.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.02/10.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.02/10.56  
% 18.02/10.58  tff(f_76, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 18.02/10.58  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 18.02/10.58  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 18.02/10.58  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 18.02/10.58  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 18.02/10.58  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.02/10.58  tff(f_41, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 18.02/10.58  tff(f_65, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 18.02/10.58  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 18.02/10.58  tff(f_67, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.02/10.58  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 18.02/10.58  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 18.02/10.58  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.02/10.58  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 18.02/10.58  tff(f_57, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 18.02/10.58  tff(c_34, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.02/10.58  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.02/10.58  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.02/10.58  tff(c_89, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k2_xboole_0(A_42, B_43))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.02/10.58  tff(c_96, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_89])).
% 18.02/10.58  tff(c_397, plain, (![A_61, B_62]: (k2_xboole_0(A_61, k4_xboole_0(B_62, A_61))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.02/10.58  tff(c_437, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=k2_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_96, c_397])).
% 18.02/10.58  tff(c_454, plain, (![A_63]: (k2_xboole_0(A_63, k1_xboole_0)=A_63)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_437])).
% 18.02/10.58  tff(c_473, plain, (![A_63]: (k2_xboole_0(k1_xboole_0, A_63)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_454, c_2])).
% 18.02/10.58  tff(c_554, plain, (![A_66]: (k2_xboole_0(k1_xboole_0, A_66)=A_66)), inference(superposition, [status(thm), theory('equality')], [c_454, c_2])).
% 18.02/10.58  tff(c_18, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.02/10.58  tff(c_565, plain, (![B_18]: (k4_xboole_0(B_18, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_18))), inference(superposition, [status(thm), theory('equality')], [c_554, c_18])).
% 18.02/10.58  tff(c_616, plain, (![B_18]: (k4_xboole_0(B_18, k1_xboole_0)=B_18)), inference(demodulation, [status(thm), theory('equality')], [c_473, c_565])).
% 18.02/10.58  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 18.02/10.58  tff(c_277, plain, (![A_57, B_58, C_59]: (r1_tarski(k3_xboole_0(A_57, B_58), k2_xboole_0(A_57, C_59)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.02/10.58  tff(c_949, plain, (![A_78, B_79]: (r1_tarski(k3_xboole_0(A_78, B_79), A_78))), inference(superposition, [status(thm), theory('equality')], [c_10, c_277])).
% 18.02/10.58  tff(c_970, plain, (![B_4, A_3]: (r1_tarski(k3_xboole_0(B_4, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_949])).
% 18.02/10.58  tff(c_307, plain, (![A_7, B_58]: (r1_tarski(k3_xboole_0(A_7, B_58), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_277])).
% 18.02/10.58  tff(c_36, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.02/10.58  tff(c_1020, plain, (![A_82, B_83, C_84]: (k1_xboole_0=A_82 | ~r1_xboole_0(B_83, C_84) | ~r1_tarski(A_82, C_84) | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_65])).
% 18.02/10.58  tff(c_1255, plain, (![A_90]: (k1_xboole_0=A_90 | ~r1_tarski(A_90, '#skF_2') | ~r1_tarski(A_90, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_1020])).
% 18.02/10.58  tff(c_2665, plain, (![B_121]: (k3_xboole_0('#skF_2', B_121)=k1_xboole_0 | ~r1_tarski(k3_xboole_0('#skF_2', B_121), '#skF_4'))), inference(resolution, [status(thm)], [c_307, c_1255])).
% 18.02/10.58  tff(c_2687, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_970, c_2665])).
% 18.02/10.58  tff(c_24, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k3_xboole_0(A_24, B_25))=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.02/10.58  tff(c_2734, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2687, c_24])).
% 18.02/10.58  tff(c_2767, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_616, c_2734])).
% 18.02/10.58  tff(c_40, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.02/10.58  tff(c_41, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 18.02/10.58  tff(c_116, plain, (![B_45, A_46]: (k2_xboole_0(B_45, A_46)=k2_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.02/10.58  tff(c_32, plain, (![A_34, B_35]: (r1_tarski(A_34, k2_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.02/10.58  tff(c_161, plain, (![A_47, B_48]: (r1_tarski(A_47, k2_xboole_0(B_48, A_47)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_32])).
% 18.02/10.58  tff(c_170, plain, (r1_tarski('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_41, c_161])).
% 18.02/10.58  tff(c_899, plain, (![A_75, B_76, C_77]: (r1_tarski(k4_xboole_0(A_75, B_76), C_77) | ~r1_tarski(A_75, k2_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.02/10.58  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.02/10.58  tff(c_13372, plain, (![A_257, B_258, C_259]: (k2_xboole_0(k4_xboole_0(A_257, B_258), C_259)=C_259 | ~r1_tarski(A_257, k2_xboole_0(B_258, C_259)))), inference(resolution, [status(thm)], [c_899, c_12])).
% 18.02/10.58  tff(c_13542, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_4'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_170, c_13372])).
% 18.02/10.58  tff(c_13621, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2767, c_13542])).
% 18.02/10.58  tff(c_137, plain, (![A_46, B_45]: (r1_tarski(A_46, k2_xboole_0(B_45, A_46)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_32])).
% 18.02/10.58  tff(c_13693, plain, (r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13621, c_137])).
% 18.02/10.58  tff(c_13723, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_13693, c_12])).
% 18.02/10.58  tff(c_51, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.02/10.58  tff(c_54, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_51])).
% 18.02/10.58  tff(c_44792, plain, (![B_426, C_427]: (k2_xboole_0(k4_xboole_0(k2_xboole_0(B_426, C_427), B_426), C_427)=C_427)), inference(resolution, [status(thm)], [c_54, c_13372])).
% 18.02/10.58  tff(c_45098, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1'), '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_41, c_44792])).
% 18.02/10.58  tff(c_22, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.02/10.58  tff(c_634, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k4_xboole_0(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_55])).
% 18.02/10.58  tff(c_675, plain, (![A_22, B_23]: (k3_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k4_xboole_0(A_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_634])).
% 18.02/10.58  tff(c_4758, plain, (![A_150, B_151]: (k3_xboole_0(A_150, k2_xboole_0(A_150, B_151))=A_150)), inference(demodulation, [status(thm), theory('equality')], [c_616, c_675])).
% 18.02/10.58  tff(c_4901, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4758])).
% 18.02/10.58  tff(c_134, plain, (![B_45, A_46]: (k4_xboole_0(B_45, k2_xboole_0(A_46, B_45))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_116, c_22])).
% 18.02/10.58  tff(c_13690, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13621, c_134])).
% 18.02/10.58  tff(c_26, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 18.02/10.58  tff(c_13790, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13690, c_26])).
% 18.02/10.58  tff(c_13819, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_616, c_4, c_13790])).
% 18.02/10.58  tff(c_1081, plain, (![A_86, B_87]: (k2_xboole_0(k3_xboole_0(A_86, B_87), A_86)=A_86)), inference(resolution, [status(thm)], [c_949, c_12])).
% 18.02/10.58  tff(c_1100, plain, (![A_86, B_87]: (k2_xboole_0(A_86, k3_xboole_0(A_86, B_87))=A_86)), inference(superposition, [status(thm), theory('equality')], [c_1081, c_2])).
% 18.02/10.58  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.02/10.58  tff(c_240, plain, (![A_55, B_56]: (k3_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.02/10.58  tff(c_252, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_240])).
% 18.02/10.58  tff(c_260, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_252, c_4])).
% 18.02/10.58  tff(c_804, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.02/10.58  tff(c_833, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_260, c_804])).
% 18.02/10.58  tff(c_854, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_616, c_833])).
% 18.02/10.58  tff(c_1722, plain, (![A_103, B_104, C_105]: (k2_xboole_0(k4_xboole_0(A_103, B_104), k3_xboole_0(A_103, C_105))=k4_xboole_0(A_103, k4_xboole_0(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.02/10.58  tff(c_1778, plain, (![C_105]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_105))=k2_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_105)))), inference(superposition, [status(thm), theory('equality')], [c_854, c_1722])).
% 18.02/10.58  tff(c_1972, plain, (![C_110]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_3', C_110))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_1778])).
% 18.02/10.58  tff(c_2002, plain, (![B_27]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_3', B_27))='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1972])).
% 18.02/10.58  tff(c_14040, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_13819, c_2002])).
% 18.02/10.58  tff(c_18534, plain, (![A_294, B_295, B_296]: (k2_xboole_0(k4_xboole_0(A_294, B_295), k3_xboole_0(B_296, A_294))=k4_xboole_0(A_294, k4_xboole_0(B_295, B_296)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1722])).
% 18.02/10.58  tff(c_50964, plain, (![B_459, A_460, B_461]: (r1_tarski(k3_xboole_0(B_459, A_460), k4_xboole_0(A_460, k4_xboole_0(B_461, B_459))))), inference(superposition, [status(thm), theory('equality')], [c_18534, c_137])).
% 18.02/10.58  tff(c_62985, plain, (![A_554]: (r1_tarski(k3_xboole_0('#skF_2', A_554), k4_xboole_0(A_554, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_14040, c_50964])).
% 18.02/10.58  tff(c_67480, plain, (![B_585]: (r1_tarski('#skF_2', k4_xboole_0(k2_xboole_0(B_585, '#skF_2'), '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4901, c_62985])).
% 18.02/10.58  tff(c_67548, plain, (r1_tarski('#skF_2', k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_41, c_67480])).
% 18.02/10.58  tff(c_13567, plain, (![A_257, A_7]: (k2_xboole_0(k4_xboole_0(A_257, A_7), A_7)=A_7 | ~r1_tarski(A_257, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_13372])).
% 18.02/10.58  tff(c_13629, plain, (![A_7, A_257]: (k2_xboole_0(A_7, A_257)=A_7 | ~r1_tarski(A_257, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2, c_13567])).
% 18.02/10.58  tff(c_67580, plain, (k2_xboole_0(k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1'), '#skF_2')=k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_67548, c_13629])).
% 18.02/10.58  tff(c_67590, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_45098, c_67580])).
% 18.02/10.58  tff(c_47435, plain, (![A_439, C_440, B_441]: (r1_tarski(k3_xboole_0(A_439, C_440), k4_xboole_0(A_439, k4_xboole_0(B_441, C_440))))), inference(superposition, [status(thm), theory('equality')], [c_1722, c_137])).
% 18.02/10.58  tff(c_48944, plain, (![A_446]: (r1_tarski(k3_xboole_0(A_446, '#skF_3'), k4_xboole_0(A_446, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_854, c_47435])).
% 18.02/10.58  tff(c_50655, plain, (![A_456]: (r1_tarski(k3_xboole_0('#skF_3', A_456), k4_xboole_0(A_456, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_48944])).
% 18.02/10.58  tff(c_50696, plain, (![B_2]: (r1_tarski('#skF_3', k4_xboole_0(k2_xboole_0(B_2, '#skF_3'), '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4901, c_50655])).
% 18.02/10.58  tff(c_67614, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_67590, c_50696])).
% 18.02/10.58  tff(c_67781, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_67614, c_13629])).
% 18.02/10.58  tff(c_67794, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13723, c_67781])).
% 18.02/10.58  tff(c_67796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_67794])).
% 18.02/10.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.02/10.58  
% 18.02/10.58  Inference rules
% 18.02/10.58  ----------------------
% 18.02/10.58  #Ref     : 0
% 18.02/10.58  #Sup     : 16801
% 18.02/10.58  #Fact    : 0
% 18.02/10.58  #Define  : 0
% 18.02/10.58  #Split   : 8
% 18.02/10.58  #Chain   : 0
% 18.02/10.58  #Close   : 0
% 18.02/10.58  
% 18.02/10.58  Ordering : KBO
% 18.02/10.58  
% 18.02/10.58  Simplification rules
% 18.02/10.58  ----------------------
% 18.02/10.58  #Subsume      : 510
% 18.02/10.58  #Demod        : 21385
% 18.02/10.58  #Tautology    : 12133
% 18.02/10.58  #SimpNegUnit  : 2
% 18.02/10.58  #BackRed      : 5
% 18.02/10.58  
% 18.02/10.58  #Partial instantiations: 0
% 18.02/10.58  #Strategies tried      : 1
% 18.02/10.58  
% 18.02/10.58  Timing (in seconds)
% 18.02/10.59  ----------------------
% 18.02/10.59  Preprocessing        : 0.48
% 18.02/10.59  Parsing              : 0.26
% 18.02/10.59  CNF conversion       : 0.03
% 18.02/10.59  Main loop            : 9.17
% 18.02/10.59  Inferencing          : 1.24
% 18.02/10.59  Reduction            : 5.74
% 18.02/10.59  Demodulation         : 5.17
% 18.02/10.59  BG Simplification    : 0.12
% 18.02/10.59  Subsumption          : 1.69
% 18.02/10.59  Abstraction          : 0.20
% 18.02/10.59  MUC search           : 0.00
% 18.02/10.59  Cooper               : 0.00
% 18.02/10.59  Total                : 9.70
% 18.02/10.59  Index Insertion      : 0.00
% 18.02/10.59  Index Deletion       : 0.00
% 18.02/10.59  Index Matching       : 0.00
% 18.02/10.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
