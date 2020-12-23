%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:14 EST 2020

% Result     : Theorem 24.23s
% Output     : CNFRefutation 24.46s
% Verified   : 
% Statistics : Number of formulae       :  212 (1167 expanded)
%              Number of leaves         :   23 ( 393 expanded)
%              Depth                    :   23
%              Number of atoms          :  279 (2186 expanded)
%              Number of equality atoms :  140 (1455 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_30,plain,
    ( '#skF_2' != '#skF_4'
    | '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_39,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,B_41) = B_41
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_188,plain,(
    ! [B_42] : k2_xboole_0(B_42,B_42) = B_42 ),
    inference(resolution,[status(thm)],[c_10,c_167])).

tff(c_16,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_197,plain,(
    ! [B_42] : k3_xboole_0(B_42,B_42) = B_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_16])).

tff(c_112,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_127,plain,(
    ! [A_37,B_36] : k3_xboole_0(A_37,k2_xboole_0(B_36,A_37)) = A_37 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_16])).

tff(c_28,plain,(
    ! [A_21,C_23,B_22,D_24] : k3_xboole_0(k2_zfmisc_1(A_21,C_23),k2_zfmisc_1(B_22,D_24)) = k2_zfmisc_1(k3_xboole_0(A_21,B_22),k3_xboole_0(C_23,D_24)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_75831,plain,(
    ! [A_806,C_807,B_808,D_809] : k3_xboole_0(k2_zfmisc_1(A_806,C_807),k2_zfmisc_1(B_808,D_809)) = k2_zfmisc_1(k3_xboole_0(A_806,B_808),k3_xboole_0(C_807,D_809)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75887,plain,(
    ! [B_808,D_809] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(B_808,D_809)) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_808),k3_xboole_0('#skF_4',D_809)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_75831])).

tff(c_75906,plain,(
    ! [B_808,D_809] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_808),k3_xboole_0('#skF_4',D_809)) = k2_zfmisc_1(k3_xboole_0('#skF_1',B_808),k3_xboole_0('#skF_2',D_809)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_75887])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78641,plain,(
    ! [A_862,B_863,C_864,D_865] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_862,B_863),k3_xboole_0(C_864,D_865)),k2_zfmisc_1(A_862,C_864)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75831,c_14])).

tff(c_86727,plain,(
    ! [A_944,B_945,A_946,B_947] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_944,B_945),k3_xboole_0(A_946,B_947)),k2_zfmisc_1(A_944,B_947)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_78641])).

tff(c_95411,plain,(
    ! [B_1000,D_1001] : r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_1',B_1000),k3_xboole_0('#skF_2',D_1001)),k2_zfmisc_1('#skF_3',D_1001)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75906,c_86727])).

tff(c_95534,plain,(
    ! [D_1002] : r1_tarski(k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2',D_1002)),k2_zfmisc_1('#skF_3',D_1002)) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_95411])).

tff(c_95587,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_95534])).

tff(c_22,plain,(
    ! [B_16,A_15,C_17] :
      ( ~ r1_tarski(k2_zfmisc_1(B_16,A_15),k2_zfmisc_1(C_17,A_15))
      | r1_tarski(B_16,C_17)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_95611,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_95587,c_22])).

tff(c_95620,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_95611])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95625,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_95620,c_6])).

tff(c_95631,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_95625])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_225,plain,(
    ! [A_44,B_45] : k2_xboole_0(k3_xboole_0(A_44,B_45),A_44) = A_44 ),
    inference(resolution,[status(thm)],[c_14,c_167])).

tff(c_37520,plain,(
    ! [A_458,B_459] : k3_xboole_0(k3_xboole_0(A_458,B_459),A_458) = k3_xboole_0(A_458,B_459) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_16])).

tff(c_38128,plain,(
    ! [B_472,A_473] : k3_xboole_0(k3_xboole_0(B_472,A_473),A_473) = k3_xboole_0(A_473,B_472) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37520])).

tff(c_38187,plain,(
    ! [B_36,A_37] : k3_xboole_0(k2_xboole_0(B_36,A_37),A_37) = k3_xboole_0(A_37,k2_xboole_0(B_36,A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_38128])).

tff(c_75508,plain,(
    ! [B_800,A_801] : k3_xboole_0(k2_xboole_0(B_800,A_801),A_801) = A_801 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_38187])).

tff(c_75586,plain,(
    ! [B_2,A_1] : k3_xboole_0(k2_xboole_0(B_2,A_1),B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75508])).

tff(c_449,plain,(
    ! [B_54,A_55,C_56] :
      ( ~ r1_tarski(k2_zfmisc_1(B_54,A_55),k2_zfmisc_1(C_56,A_55))
      | r1_tarski(B_54,C_56)
      | k1_xboole_0 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_455,plain,(
    ! [B_54] :
      ( ~ r1_tarski(k2_zfmisc_1(B_54,'#skF_4'),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_54,'#skF_3')
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_449])).

tff(c_465,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_468,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_34])).

tff(c_467,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_32])).

tff(c_187,plain,(
    ! [B_6] : k2_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_167])).

tff(c_1362,plain,(
    ! [C_82,A_83,B_84] : k2_xboole_0(k2_zfmisc_1(C_82,A_83),k2_zfmisc_1(C_82,B_84)) = k2_zfmisc_1(C_82,k2_xboole_0(A_83,B_84)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1763,plain,(
    ! [B_91] : k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',B_91)) = k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1362])).

tff(c_32908,plain,(
    ! [B_431] : k3_xboole_0(k2_zfmisc_1('#skF_3',B_431),k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_431))) = k2_zfmisc_1('#skF_3',B_431) ),
    inference(superposition,[status(thm),theory(equality)],[c_1763,c_127])).

tff(c_33131,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4','#skF_4'))) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_32908])).

tff(c_33187,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_36,c_28,c_187,c_33131])).

tff(c_1968,plain,(
    ! [A_94,C_95,B_96,D_97] : k3_xboole_0(k2_zfmisc_1(A_94,C_95),k2_zfmisc_1(B_96,D_97)) = k2_zfmisc_1(k3_xboole_0(A_94,B_96),k3_xboole_0(C_95,D_97)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_23793,plain,(
    ! [B_366,D_367,A_368,C_369] : k3_xboole_0(k2_zfmisc_1(B_366,D_367),k2_zfmisc_1(A_368,C_369)) = k2_zfmisc_1(k3_xboole_0(A_368,B_366),k3_xboole_0(C_369,D_367)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1968,c_4])).

tff(c_23895,plain,(
    ! [A_368,B_366,C_369,D_367] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_368,B_366),k3_xboole_0(C_369,D_367)),k2_zfmisc_1(B_366,D_367)) ),
    inference(superposition,[status(thm),theory(equality)],[c_23793,c_14])).

tff(c_33208,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33187,c_23895])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( ~ r1_tarski(k2_zfmisc_1(A_15,B_16),k2_zfmisc_1(A_15,C_17))
      | r1_tarski(B_16,C_17)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_799,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_tarski(k2_zfmisc_1(A_68,B_69),k2_zfmisc_1(A_68,C_70))
      | r1_tarski(B_69,C_70)
      | A_68 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_20])).

tff(c_802,plain,(
    ! [C_70] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',C_70))
      | r1_tarski('#skF_4',C_70)
      | '#skF_3' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_799])).

tff(c_3942,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_802])).

tff(c_3949,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3942,c_36])).

tff(c_526,plain,(
    ! [A_59,C_60,B_61] : k2_xboole_0(k2_zfmisc_1(A_59,C_60),k2_zfmisc_1(B_61,C_60)) = k2_zfmisc_1(k2_xboole_0(A_59,B_61),C_60) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3572,plain,(
    ! [A_123] : k2_xboole_0(k2_zfmisc_1(A_123,'#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1(k2_xboole_0(A_123,'#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_526])).

tff(c_3628,plain,(
    ! [A_123] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0(A_123,'#skF_3'),'#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3572,c_127])).

tff(c_18230,plain,(
    ! [A_298] : k2_zfmisc_1(k3_xboole_0('#skF_1',k2_xboole_0(A_298,'#skF_4')),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3949,c_4,c_28,c_3942,c_3628])).

tff(c_2017,plain,(
    ! [A_94,B_96,C_95,D_97] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_94,B_96),k3_xboole_0(C_95,D_97)),k2_zfmisc_1(A_94,C_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1968,c_14])).

tff(c_18345,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18230,c_2017])).

tff(c_798,plain,(
    ! [A_15,B_16,C_17] :
      ( ~ r1_tarski(k2_zfmisc_1(A_15,B_16),k2_zfmisc_1(A_15,C_17))
      | r1_tarski(B_16,C_17)
      | A_15 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_20])).

tff(c_3976,plain,(
    ! [C_17] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_1',C_17))
      | r1_tarski('#skF_2',C_17)
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3949,c_798])).

tff(c_3990,plain,(
    ! [C_17] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_1',C_17))
      | r1_tarski('#skF_2',C_17) ) ),
    inference(negUnitSimplification,[status(thm)],[c_468,c_3976])).

tff(c_19416,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_18345,c_3990])).

tff(c_19424,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_19416,c_6])).

tff(c_19430,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_467,c_19424])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_19431,plain,(
    k2_xboole_0('#skF_2','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_19416,c_12])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_581,plain,(
    ! [A_62,B_63] : k2_xboole_0(A_62,k2_xboole_0(A_62,B_63)) = k2_xboole_0(A_62,B_63) ),
    inference(resolution,[status(thm)],[c_18,c_167])).

tff(c_812,plain,(
    ! [A_71,B_72] : k2_xboole_0(A_71,k2_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_581])).

tff(c_7980,plain,(
    ! [B_202,A_203] : k3_xboole_0(k2_xboole_0(B_202,A_203),k2_xboole_0(A_203,B_202)) = k2_xboole_0(B_202,A_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_812,c_127])).

tff(c_8201,plain,(
    ! [A_203,B_202] : k3_xboole_0(k2_xboole_0(A_203,B_202),k2_xboole_0(B_202,A_203)) = k2_xboole_0(B_202,A_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7980])).

tff(c_19491,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_2')) = k2_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_19431,c_8201])).

tff(c_19632,plain,(
    k2_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_19491])).

tff(c_1807,plain,(
    ! [B_91] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_91))) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1763,c_16])).

tff(c_17550,plain,(
    ! [B_297] : k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_1'),k3_xboole_0('#skF_2',k2_xboole_0('#skF_4',B_297))) = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3949,c_4,c_28,c_3942,c_1807])).

tff(c_17665,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17550,c_2017])).

tff(c_6418,plain,(
    ! [B_184,A_185,C_186] :
      ( ~ r1_tarski(k2_zfmisc_1(B_184,A_185),k2_zfmisc_1(C_186,A_185))
      | r1_tarski(B_184,C_186)
      | A_185 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_22])).

tff(c_6442,plain,(
    ! [C_186] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1(C_186,'#skF_2'))
      | r1_tarski('#skF_1',C_186)
      | '#skF_2' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3949,c_6418])).

tff(c_6463,plain,(
    ! [C_186] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1(C_186,'#skF_2'))
      | r1_tarski('#skF_1',C_186) ) ),
    inference(negUnitSimplification,[status(thm)],[c_467,c_6442])).

tff(c_17774,plain,(
    r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_17665,c_6463])).

tff(c_17787,plain,(
    k2_xboole_0('#skF_1','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_17774,c_12])).

tff(c_17845,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_4','#skF_1')) = k2_xboole_0('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_17787,c_8201])).

tff(c_17985,plain,(
    k2_xboole_0('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_17845])).

tff(c_4193,plain,(
    ! [C_135,B_136,A_137] : k2_xboole_0(k2_zfmisc_1(C_135,B_136),k2_zfmisc_1(C_135,A_137)) = k2_zfmisc_1(C_135,k2_xboole_0(A_137,B_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1362,c_2])).

tff(c_20476,plain,(
    ! [A_303] : k2_xboole_0(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_1',A_303)) = k2_zfmisc_1('#skF_1',k2_xboole_0(A_303,'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3949,c_4193])).

tff(c_542,plain,(
    ! [B_61,C_60,A_59] : k2_xboole_0(k2_zfmisc_1(B_61,C_60),k2_zfmisc_1(A_59,C_60)) = k2_zfmisc_1(k2_xboole_0(A_59,B_61),C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_2])).

tff(c_20573,plain,(
    k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_4'),'#skF_4') = k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20476,c_542])).

tff(c_20693,plain,(
    k2_zfmisc_1('#skF_1','#skF_4') = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19632,c_17985,c_2,c_20573])).

tff(c_3979,plain,(
    ! [B_16] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1',B_16),k2_zfmisc_1('#skF_4','#skF_4'))
      | r1_tarski(B_16,'#skF_2')
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3949,c_798])).

tff(c_3991,plain,(
    ! [B_16] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1',B_16),k2_zfmisc_1('#skF_4','#skF_4'))
      | r1_tarski(B_16,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_468,c_3979])).

tff(c_20747,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_4','#skF_4'))
    | r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20693,c_3991])).

tff(c_20838,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20747])).

tff(c_20840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19430,c_20838])).

tff(c_20841,plain,(
    ! [C_70] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',C_70))
      | r1_tarski('#skF_4',C_70) ) ),
    inference(splitRight,[status(thm)],[c_802])).

tff(c_33336,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_33208,c_20841])).

tff(c_33343,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_33336,c_6])).

tff(c_33349,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_467,c_33343])).

tff(c_33274,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_33187,c_2017])).

tff(c_37237,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_33274,c_798])).

tff(c_37246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_468,c_33349,c_37237])).

tff(c_37248,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_26,plain,(
    ! [C_20,A_18,B_19] : k2_xboole_0(k2_zfmisc_1(C_20,A_18),k2_zfmisc_1(C_20,B_19)) = k2_zfmisc_1(C_20,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_37909,plain,(
    ! [A_467,C_468,B_469] : k2_xboole_0(k2_zfmisc_1(A_467,C_468),k2_zfmisc_1(B_469,C_468)) = k2_zfmisc_1(k2_xboole_0(A_467,B_469),C_468) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38637,plain,(
    ! [A_484] : k2_xboole_0(k2_zfmisc_1(A_484,'#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1(k2_xboole_0(A_484,'#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_37909])).

tff(c_38701,plain,(
    k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_3'),'#skF_4') = k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_38637])).

tff(c_133,plain,(
    ! [A_37,B_36] : r1_tarski(A_37,k2_xboole_0(B_36,A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_18])).

tff(c_183,plain,(
    ! [A_37,B_36] : k2_xboole_0(A_37,k2_xboole_0(B_36,A_37)) = k2_xboole_0(B_36,A_37) ),
    inference(resolution,[status(thm)],[c_133,c_167])).

tff(c_40523,plain,(
    ! [B_515] : k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(B_515,'#skF_4')) = k2_zfmisc_1(k2_xboole_0('#skF_3',B_515),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_37909])).

tff(c_52699,plain,(
    ! [B_645] : k3_xboole_0(k2_zfmisc_1(B_645,'#skF_4'),k2_zfmisc_1(k2_xboole_0('#skF_3',B_645),'#skF_4')) = k2_zfmisc_1(B_645,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40523,c_127])).

tff(c_52862,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_4','#skF_2')),k2_zfmisc_1(k2_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_3')),'#skF_4')) = k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38701,c_52699])).

tff(c_52970,plain,(
    k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38701,c_16,c_16,c_4,c_28,c_183,c_52862])).

tff(c_37249,plain,(
    ! [C_445,A_446,B_447] : k2_xboole_0(k2_zfmisc_1(C_445,A_446),k2_zfmisc_1(C_445,B_447)) = k2_zfmisc_1(C_445,k2_xboole_0(A_446,B_447)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_37262,plain,(
    ! [C_445,B_447,A_446] : r1_tarski(k2_zfmisc_1(C_445,B_447),k2_zfmisc_1(C_445,k2_xboole_0(A_446,B_447))) ),
    inference(superposition,[status(thm),theory(equality)],[c_37249,c_133])).

tff(c_53050,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52970,c_37262])).

tff(c_452,plain,(
    ! [C_56] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(C_56,'#skF_4'))
      | r1_tarski('#skF_3',C_56)
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_449])).

tff(c_37351,plain,(
    ! [C_56] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(C_56,'#skF_4'))
      | r1_tarski('#skF_3',C_56) ) ),
    inference(negUnitSimplification,[status(thm)],[c_37248,c_452])).

tff(c_53115,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_53050,c_37351])).

tff(c_53119,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_53115,c_6])).

tff(c_53125,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_53119])).

tff(c_37363,plain,(
    ! [A_451,B_452,C_453] :
      ( ~ r1_tarski(k2_zfmisc_1(A_451,B_452),k2_zfmisc_1(A_451,C_453))
      | r1_tarski(B_452,C_453)
      | k1_xboole_0 = A_451 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_37369,plain,(
    ! [B_452] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_3',B_452),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_452,'#skF_4')
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_37363])).

tff(c_38226,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_37369])).

tff(c_38230,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38226,c_32])).

tff(c_53126,plain,(
    k2_xboole_0('#skF_3','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_53115,c_12])).

tff(c_38236,plain,(
    ! [B_474,A_475] : k3_xboole_0(k2_xboole_0(B_474,A_475),A_475) = A_475 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_38187])).

tff(c_38314,plain,(
    ! [B_2,A_1] : k3_xboole_0(k2_xboole_0(B_2,A_1),B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_38236])).

tff(c_53234,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_53126,c_38314])).

tff(c_38221,plain,(
    ! [B_36,A_37] : k3_xboole_0(k2_xboole_0(B_36,A_37),A_37) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_38187])).

tff(c_38470,plain,(
    ! [A_478,C_479,B_480,D_481] : k3_xboole_0(k2_zfmisc_1(A_478,C_479),k2_zfmisc_1(B_480,D_481)) = k2_zfmisc_1(k3_xboole_0(A_478,B_480),k3_xboole_0(C_479,D_481)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38510,plain,(
    ! [A_478,B_480,C_479,D_481] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_478,B_480),k3_xboole_0(C_479,D_481)),k2_zfmisc_1(A_478,C_479)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38470,c_14])).

tff(c_56244,plain,(
    ! [C_658,D_659] : r1_tarski(k2_zfmisc_1('#skF_3',k3_xboole_0(C_658,D_659)),k2_zfmisc_1('#skF_1',C_658)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53234,c_38510])).

tff(c_65175,plain,(
    ! [A_746,B_747] : r1_tarski(k2_zfmisc_1('#skF_3',A_746),k2_zfmisc_1('#skF_1',k2_xboole_0(B_747,A_746))) ),
    inference(superposition,[status(thm),theory(equality)],[c_38221,c_56244])).

tff(c_65551,plain,(
    ! [B_750] : r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1',k2_xboole_0(B_750,'#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_65175])).

tff(c_38227,plain,(
    ! [A_15,B_16,C_17] :
      ( ~ r1_tarski(k2_zfmisc_1(A_15,B_16),k2_zfmisc_1(A_15,C_17))
      | r1_tarski(B_16,C_17)
      | A_15 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38226,c_20])).

tff(c_65554,plain,(
    ! [B_750] :
      ( r1_tarski('#skF_2',k2_xboole_0(B_750,'#skF_4'))
      | '#skF_3' = '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_65551,c_38227])).

tff(c_65617,plain,(
    ! [B_751] : r1_tarski('#skF_2',k2_xboole_0(B_751,'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_65554])).

tff(c_65729,plain,(
    ! [B_753] : k2_xboole_0('#skF_2',k2_xboole_0(B_753,'#skF_4')) = k2_xboole_0(B_753,'#skF_4') ),
    inference(resolution,[status(thm)],[c_65617,c_12])).

tff(c_65890,plain,(
    ! [B_753] : k3_xboole_0('#skF_2',k2_xboole_0(B_753,'#skF_4')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_65729,c_16])).

tff(c_38520,plain,(
    ! [B_480,D_481] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(B_480,D_481)) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_480),k3_xboole_0('#skF_4',D_481)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_38470])).

tff(c_45530,plain,(
    ! [B_595,D_596] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_595),k3_xboole_0('#skF_4',D_596)) = k2_zfmisc_1(k3_xboole_0('#skF_1',B_595),k3_xboole_0('#skF_2',D_596)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38520])).

tff(c_45672,plain,(
    ! [B_595,B_36] : k2_zfmisc_1(k3_xboole_0('#skF_1',B_595),k3_xboole_0('#skF_2',k2_xboole_0(B_36,'#skF_4'))) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_595),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_45530])).

tff(c_72244,plain,(
    ! [B_785] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_785),'#skF_4') = k2_zfmisc_1(k3_xboole_0('#skF_1',B_785),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65890,c_45672])).

tff(c_72454,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_72244])).

tff(c_72497,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53234,c_36,c_72454])).

tff(c_38229,plain,(
    ! [B_16,A_15,C_17] :
      ( ~ r1_tarski(k2_zfmisc_1(B_16,A_15),k2_zfmisc_1(C_17,A_15))
      | r1_tarski(B_16,C_17)
      | A_15 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38226,c_22])).

tff(c_72567,plain,(
    ! [B_16] :
      ( ~ r1_tarski(k2_zfmisc_1(B_16,'#skF_2'),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_16,'#skF_3')
      | '#skF_2' = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72497,c_38229])).

tff(c_75450,plain,(
    ! [B_799] :
      ( ~ r1_tarski(k2_zfmisc_1(B_799,'#skF_2'),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_799,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38230,c_72567])).

tff(c_75491,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_75450])).

tff(c_75505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53125,c_75491])).

tff(c_75507,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_37369])).

tff(c_37366,plain,(
    ! [C_453] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',C_453))
      | r1_tarski('#skF_4',C_453)
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_37363])).

tff(c_78025,plain,(
    ! [C_453] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',C_453))
      | r1_tarski('#skF_4',C_453) ) ),
    inference(negUnitSimplification,[status(thm)],[c_75507,c_37366])).

tff(c_95617,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_95587,c_78025])).

tff(c_95638,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_95617,c_6])).

tff(c_97662,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_95638])).

tff(c_85987,plain,(
    ! [B_939,D_940] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_939),k3_xboole_0('#skF_4',D_940)) = k2_zfmisc_1(k3_xboole_0('#skF_1',B_939),k3_xboole_0('#skF_2',D_940)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_75887])).

tff(c_106254,plain,(
    ! [B_1089,D_1090] : k2_zfmisc_1(k3_xboole_0('#skF_1',k2_xboole_0(B_1089,'#skF_3')),k3_xboole_0('#skF_2',D_1090)) = k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4',D_1090)) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_85987])).

tff(c_78739,plain,(
    ! [A_862,B_863,A_3,B_4] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_862,B_863),k3_xboole_0(A_3,B_4)),k2_zfmisc_1(A_862,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_78641])).

tff(c_110839,plain,(
    ! [D_1109] : r1_tarski(k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4',D_1109)),k2_zfmisc_1('#skF_1',D_1109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_106254,c_78739])).

tff(c_110905,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_110839])).

tff(c_110926,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_110905])).

tff(c_111252,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_110926,c_20])).

tff(c_111264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_97662,c_111252])).

tff(c_111265,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_95638])).

tff(c_78904,plain,(
    ! [A_869,B_870,A_871] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_869,B_870),A_871),k2_zfmisc_1(A_869,A_871)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_78641])).

tff(c_79337,plain,(
    ! [B_880,A_881,A_882] : r1_tarski(k2_zfmisc_1(k3_xboole_0(B_880,A_881),A_882),k2_zfmisc_1(A_881,A_882)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_78904])).

tff(c_79387,plain,(
    ! [B_880] : r1_tarski(k2_zfmisc_1(k3_xboole_0(B_880,'#skF_3'),'#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_79337])).

tff(c_113643,plain,(
    ! [B_1142] : r1_tarski(k2_zfmisc_1(k3_xboole_0(B_1142,'#skF_3'),'#skF_4'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111265,c_79387])).

tff(c_113646,plain,(
    ! [B_1142] :
      ( r1_tarski(k3_xboole_0(B_1142,'#skF_3'),'#skF_1')
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_113643,c_22])).

tff(c_113709,plain,(
    ! [B_1143] : r1_tarski(k3_xboole_0(B_1143,'#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_37248,c_113646])).

tff(c_113728,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_75586,c_113709])).

tff(c_113759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95631,c_113728])).

tff(c_113760,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_113761,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_113768,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113761,c_36])).

tff(c_114327,plain,(
    ! [A_1178,B_1179,C_1180] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1178,B_1179),k2_zfmisc_1(A_1178,C_1180))
      | r1_tarski(B_1179,C_1180)
      | k1_xboole_0 = A_1178 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_114336,plain,(
    ! [C_1180] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_1',C_1180))
      | r1_tarski('#skF_2',C_1180)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113768,c_114327])).

tff(c_114439,plain,(
    ! [C_1183] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_1',C_1183))
      | r1_tarski('#skF_2',C_1183) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_114336])).

tff(c_114458,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_114439])).

tff(c_114460,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_114458,c_6])).

tff(c_114466,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_113760,c_114460])).

tff(c_114339,plain,(
    ! [B_1179] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1',B_1179),k2_zfmisc_1('#skF_1','#skF_4'))
      | r1_tarski(B_1179,'#skF_2')
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113768,c_114327])).

tff(c_114643,plain,(
    ! [B_1187] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1',B_1187),k2_zfmisc_1('#skF_1','#skF_4'))
      | r1_tarski(B_1187,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_114339])).

tff(c_114653,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_114643])).

tff(c_114659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114466,c_114653])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.23/16.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.33/16.12  
% 24.33/16.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.33/16.12  %$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 24.33/16.12  
% 24.33/16.12  %Foreground sorts:
% 24.33/16.12  
% 24.33/16.12  
% 24.33/16.12  %Background operators:
% 24.33/16.12  
% 24.33/16.12  
% 24.33/16.12  %Foreground operators:
% 24.33/16.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.33/16.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.33/16.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.33/16.12  tff('#skF_2', type, '#skF_2': $i).
% 24.33/16.12  tff('#skF_3', type, '#skF_3': $i).
% 24.33/16.12  tff('#skF_1', type, '#skF_1': $i).
% 24.33/16.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.33/16.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 24.33/16.12  tff('#skF_4', type, '#skF_4': $i).
% 24.33/16.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.33/16.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.33/16.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.33/16.12  
% 24.46/16.15  tff(f_73, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 24.46/16.15  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.46/16.15  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 24.46/16.15  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 24.46/16.15  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 24.46/16.15  tff(f_62, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 24.46/16.15  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 24.46/16.15  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 24.46/16.15  tff(f_56, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 24.46/16.15  tff(f_60, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 24.46/16.15  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 24.46/16.15  tff(c_30, plain, ('#skF_2'!='#skF_4' | '#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 24.46/16.15  tff(c_39, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_30])).
% 24.46/16.15  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 24.46/16.15  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.46/16.15  tff(c_167, plain, (![A_40, B_41]: (k2_xboole_0(A_40, B_41)=B_41 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.46/16.15  tff(c_188, plain, (![B_42]: (k2_xboole_0(B_42, B_42)=B_42)), inference(resolution, [status(thm)], [c_10, c_167])).
% 24.46/16.15  tff(c_16, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 24.46/16.15  tff(c_197, plain, (![B_42]: (k3_xboole_0(B_42, B_42)=B_42)), inference(superposition, [status(thm), theory('equality')], [c_188, c_16])).
% 24.46/16.15  tff(c_112, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 24.46/16.15  tff(c_127, plain, (![A_37, B_36]: (k3_xboole_0(A_37, k2_xboole_0(B_36, A_37))=A_37)), inference(superposition, [status(thm), theory('equality')], [c_112, c_16])).
% 24.46/16.15  tff(c_28, plain, (![A_21, C_23, B_22, D_24]: (k3_xboole_0(k2_zfmisc_1(A_21, C_23), k2_zfmisc_1(B_22, D_24))=k2_zfmisc_1(k3_xboole_0(A_21, B_22), k3_xboole_0(C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 24.46/16.15  tff(c_36, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 24.46/16.15  tff(c_75831, plain, (![A_806, C_807, B_808, D_809]: (k3_xboole_0(k2_zfmisc_1(A_806, C_807), k2_zfmisc_1(B_808, D_809))=k2_zfmisc_1(k3_xboole_0(A_806, B_808), k3_xboole_0(C_807, D_809)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 24.46/16.15  tff(c_75887, plain, (![B_808, D_809]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(B_808, D_809))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_808), k3_xboole_0('#skF_4', D_809)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_75831])).
% 24.46/16.15  tff(c_75906, plain, (![B_808, D_809]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_808), k3_xboole_0('#skF_4', D_809))=k2_zfmisc_1(k3_xboole_0('#skF_1', B_808), k3_xboole_0('#skF_2', D_809)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_75887])).
% 24.46/16.15  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 24.46/16.15  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 24.46/16.15  tff(c_78641, plain, (![A_862, B_863, C_864, D_865]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_862, B_863), k3_xboole_0(C_864, D_865)), k2_zfmisc_1(A_862, C_864)))), inference(superposition, [status(thm), theory('equality')], [c_75831, c_14])).
% 24.46/16.15  tff(c_86727, plain, (![A_944, B_945, A_946, B_947]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_944, B_945), k3_xboole_0(A_946, B_947)), k2_zfmisc_1(A_944, B_947)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_78641])).
% 24.46/16.15  tff(c_95411, plain, (![B_1000, D_1001]: (r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_1', B_1000), k3_xboole_0('#skF_2', D_1001)), k2_zfmisc_1('#skF_3', D_1001)))), inference(superposition, [status(thm), theory('equality')], [c_75906, c_86727])).
% 24.46/16.15  tff(c_95534, plain, (![D_1002]: (r1_tarski(k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', D_1002)), k2_zfmisc_1('#skF_3', D_1002)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_95411])).
% 24.46/16.15  tff(c_95587, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_197, c_95534])).
% 24.46/16.15  tff(c_22, plain, (![B_16, A_15, C_17]: (~r1_tarski(k2_zfmisc_1(B_16, A_15), k2_zfmisc_1(C_17, A_15)) | r1_tarski(B_16, C_17) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 24.46/16.15  tff(c_95611, plain, (r1_tarski('#skF_1', '#skF_3') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_95587, c_22])).
% 24.46/16.15  tff(c_95620, plain, (r1_tarski('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_95611])).
% 24.46/16.15  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.46/16.15  tff(c_95625, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_95620, c_6])).
% 24.46/16.15  tff(c_95631, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_39, c_95625])).
% 24.46/16.15  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 24.46/16.15  tff(c_225, plain, (![A_44, B_45]: (k2_xboole_0(k3_xboole_0(A_44, B_45), A_44)=A_44)), inference(resolution, [status(thm)], [c_14, c_167])).
% 24.46/16.15  tff(c_37520, plain, (![A_458, B_459]: (k3_xboole_0(k3_xboole_0(A_458, B_459), A_458)=k3_xboole_0(A_458, B_459))), inference(superposition, [status(thm), theory('equality')], [c_225, c_16])).
% 24.46/16.15  tff(c_38128, plain, (![B_472, A_473]: (k3_xboole_0(k3_xboole_0(B_472, A_473), A_473)=k3_xboole_0(A_473, B_472))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37520])).
% 24.46/16.15  tff(c_38187, plain, (![B_36, A_37]: (k3_xboole_0(k2_xboole_0(B_36, A_37), A_37)=k3_xboole_0(A_37, k2_xboole_0(B_36, A_37)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_38128])).
% 24.46/16.15  tff(c_75508, plain, (![B_800, A_801]: (k3_xboole_0(k2_xboole_0(B_800, A_801), A_801)=A_801)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_38187])).
% 24.46/16.15  tff(c_75586, plain, (![B_2, A_1]: (k3_xboole_0(k2_xboole_0(B_2, A_1), B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_75508])).
% 24.46/16.15  tff(c_449, plain, (![B_54, A_55, C_56]: (~r1_tarski(k2_zfmisc_1(B_54, A_55), k2_zfmisc_1(C_56, A_55)) | r1_tarski(B_54, C_56) | k1_xboole_0=A_55)), inference(cnfTransformation, [status(thm)], [f_56])).
% 24.46/16.15  tff(c_455, plain, (![B_54]: (~r1_tarski(k2_zfmisc_1(B_54, '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_54, '#skF_3') | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_449])).
% 24.46/16.15  tff(c_465, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_455])).
% 24.46/16.15  tff(c_34, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 24.46/16.15  tff(c_468, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_465, c_34])).
% 24.46/16.15  tff(c_467, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_465, c_32])).
% 24.46/16.15  tff(c_187, plain, (![B_6]: (k2_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_167])).
% 24.46/16.15  tff(c_1362, plain, (![C_82, A_83, B_84]: (k2_xboole_0(k2_zfmisc_1(C_82, A_83), k2_zfmisc_1(C_82, B_84))=k2_zfmisc_1(C_82, k2_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.46/16.15  tff(c_1763, plain, (![B_91]: (k2_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', B_91))=k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_91)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1362])).
% 24.46/16.15  tff(c_32908, plain, (![B_431]: (k3_xboole_0(k2_zfmisc_1('#skF_3', B_431), k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_431)))=k2_zfmisc_1('#skF_3', B_431))), inference(superposition, [status(thm), theory('equality')], [c_1763, c_127])).
% 24.46/16.15  tff(c_33131, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', '#skF_4')))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_32908])).
% 24.46/16.15  tff(c_33187, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_36, c_28, c_187, c_33131])).
% 24.46/16.15  tff(c_1968, plain, (![A_94, C_95, B_96, D_97]: (k3_xboole_0(k2_zfmisc_1(A_94, C_95), k2_zfmisc_1(B_96, D_97))=k2_zfmisc_1(k3_xboole_0(A_94, B_96), k3_xboole_0(C_95, D_97)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 24.46/16.15  tff(c_23793, plain, (![B_366, D_367, A_368, C_369]: (k3_xboole_0(k2_zfmisc_1(B_366, D_367), k2_zfmisc_1(A_368, C_369))=k2_zfmisc_1(k3_xboole_0(A_368, B_366), k3_xboole_0(C_369, D_367)))), inference(superposition, [status(thm), theory('equality')], [c_1968, c_4])).
% 24.46/16.15  tff(c_23895, plain, (![A_368, B_366, C_369, D_367]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_368, B_366), k3_xboole_0(C_369, D_367)), k2_zfmisc_1(B_366, D_367)))), inference(superposition, [status(thm), theory('equality')], [c_23793, c_14])).
% 24.46/16.15  tff(c_33208, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_33187, c_23895])).
% 24.46/16.15  tff(c_20, plain, (![A_15, B_16, C_17]: (~r1_tarski(k2_zfmisc_1(A_15, B_16), k2_zfmisc_1(A_15, C_17)) | r1_tarski(B_16, C_17) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 24.46/16.15  tff(c_799, plain, (![A_68, B_69, C_70]: (~r1_tarski(k2_zfmisc_1(A_68, B_69), k2_zfmisc_1(A_68, C_70)) | r1_tarski(B_69, C_70) | A_68='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_20])).
% 24.46/16.15  tff(c_802, plain, (![C_70]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', C_70)) | r1_tarski('#skF_4', C_70) | '#skF_3'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_799])).
% 24.46/16.15  tff(c_3942, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_802])).
% 24.46/16.15  tff(c_3949, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3942, c_36])).
% 24.46/16.15  tff(c_526, plain, (![A_59, C_60, B_61]: (k2_xboole_0(k2_zfmisc_1(A_59, C_60), k2_zfmisc_1(B_61, C_60))=k2_zfmisc_1(k2_xboole_0(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.46/16.15  tff(c_3572, plain, (![A_123]: (k2_xboole_0(k2_zfmisc_1(A_123, '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1(k2_xboole_0(A_123, '#skF_3'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_526])).
% 24.46/16.15  tff(c_3628, plain, (![A_123]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0(A_123, '#skF_3'), '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3572, c_127])).
% 24.46/16.15  tff(c_18230, plain, (![A_298]: (k2_zfmisc_1(k3_xboole_0('#skF_1', k2_xboole_0(A_298, '#skF_4')), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3949, c_4, c_28, c_3942, c_3628])).
% 24.46/16.15  tff(c_2017, plain, (![A_94, B_96, C_95, D_97]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_94, B_96), k3_xboole_0(C_95, D_97)), k2_zfmisc_1(A_94, C_95)))), inference(superposition, [status(thm), theory('equality')], [c_1968, c_14])).
% 24.46/16.15  tff(c_18345, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_18230, c_2017])).
% 24.46/16.15  tff(c_798, plain, (![A_15, B_16, C_17]: (~r1_tarski(k2_zfmisc_1(A_15, B_16), k2_zfmisc_1(A_15, C_17)) | r1_tarski(B_16, C_17) | A_15='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_20])).
% 24.46/16.15  tff(c_3976, plain, (![C_17]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_1', C_17)) | r1_tarski('#skF_2', C_17) | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3949, c_798])).
% 24.46/16.15  tff(c_3990, plain, (![C_17]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_1', C_17)) | r1_tarski('#skF_2', C_17))), inference(negUnitSimplification, [status(thm)], [c_468, c_3976])).
% 24.46/16.15  tff(c_19416, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_18345, c_3990])).
% 24.46/16.15  tff(c_19424, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_19416, c_6])).
% 24.46/16.15  tff(c_19430, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_467, c_19424])).
% 24.46/16.15  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.46/16.15  tff(c_19431, plain, (k2_xboole_0('#skF_2', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_19416, c_12])).
% 24.46/16.15  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 24.46/16.15  tff(c_581, plain, (![A_62, B_63]: (k2_xboole_0(A_62, k2_xboole_0(A_62, B_63))=k2_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_18, c_167])).
% 24.46/16.15  tff(c_812, plain, (![A_71, B_72]: (k2_xboole_0(A_71, k2_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(superposition, [status(thm), theory('equality')], [c_2, c_581])).
% 24.46/16.15  tff(c_7980, plain, (![B_202, A_203]: (k3_xboole_0(k2_xboole_0(B_202, A_203), k2_xboole_0(A_203, B_202))=k2_xboole_0(B_202, A_203))), inference(superposition, [status(thm), theory('equality')], [c_812, c_127])).
% 24.46/16.15  tff(c_8201, plain, (![A_203, B_202]: (k3_xboole_0(k2_xboole_0(A_203, B_202), k2_xboole_0(B_202, A_203))=k2_xboole_0(B_202, A_203))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7980])).
% 24.46/16.15  tff(c_19491, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_2'))=k2_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_19431, c_8201])).
% 24.46/16.15  tff(c_19632, plain, (k2_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_19491])).
% 24.46/16.15  tff(c_1807, plain, (![B_91]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_91)))=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1763, c_16])).
% 24.46/16.15  tff(c_17550, plain, (![B_297]: (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_1'), k3_xboole_0('#skF_2', k2_xboole_0('#skF_4', B_297)))=k2_zfmisc_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3949, c_4, c_28, c_3942, c_1807])).
% 24.46/16.15  tff(c_17665, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17550, c_2017])).
% 24.46/16.15  tff(c_6418, plain, (![B_184, A_185, C_186]: (~r1_tarski(k2_zfmisc_1(B_184, A_185), k2_zfmisc_1(C_186, A_185)) | r1_tarski(B_184, C_186) | A_185='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_22])).
% 24.46/16.15  tff(c_6442, plain, (![C_186]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1(C_186, '#skF_2')) | r1_tarski('#skF_1', C_186) | '#skF_2'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3949, c_6418])).
% 24.46/16.15  tff(c_6463, plain, (![C_186]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1(C_186, '#skF_2')) | r1_tarski('#skF_1', C_186))), inference(negUnitSimplification, [status(thm)], [c_467, c_6442])).
% 24.46/16.15  tff(c_17774, plain, (r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_17665, c_6463])).
% 24.46/16.15  tff(c_17787, plain, (k2_xboole_0('#skF_1', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_17774, c_12])).
% 24.46/16.15  tff(c_17845, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_4', '#skF_1'))=k2_xboole_0('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17787, c_8201])).
% 24.46/16.15  tff(c_17985, plain, (k2_xboole_0('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_17845])).
% 24.46/16.15  tff(c_4193, plain, (![C_135, B_136, A_137]: (k2_xboole_0(k2_zfmisc_1(C_135, B_136), k2_zfmisc_1(C_135, A_137))=k2_zfmisc_1(C_135, k2_xboole_0(A_137, B_136)))), inference(superposition, [status(thm), theory('equality')], [c_1362, c_2])).
% 24.46/16.15  tff(c_20476, plain, (![A_303]: (k2_xboole_0(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_1', A_303))=k2_zfmisc_1('#skF_1', k2_xboole_0(A_303, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_3949, c_4193])).
% 24.46/16.15  tff(c_542, plain, (![B_61, C_60, A_59]: (k2_xboole_0(k2_zfmisc_1(B_61, C_60), k2_zfmisc_1(A_59, C_60))=k2_zfmisc_1(k2_xboole_0(A_59, B_61), C_60))), inference(superposition, [status(thm), theory('equality')], [c_526, c_2])).
% 24.46/16.15  tff(c_20573, plain, (k2_zfmisc_1(k2_xboole_0('#skF_1', '#skF_4'), '#skF_4')=k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_20476, c_542])).
% 24.46/16.15  tff(c_20693, plain, (k2_zfmisc_1('#skF_1', '#skF_4')=k2_zfmisc_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19632, c_17985, c_2, c_20573])).
% 24.46/16.15  tff(c_3979, plain, (![B_16]: (~r1_tarski(k2_zfmisc_1('#skF_1', B_16), k2_zfmisc_1('#skF_4', '#skF_4')) | r1_tarski(B_16, '#skF_2') | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3949, c_798])).
% 24.46/16.15  tff(c_3991, plain, (![B_16]: (~r1_tarski(k2_zfmisc_1('#skF_1', B_16), k2_zfmisc_1('#skF_4', '#skF_4')) | r1_tarski(B_16, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_468, c_3979])).
% 24.46/16.15  tff(c_20747, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4')) | r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20693, c_3991])).
% 24.46/16.15  tff(c_20838, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20747])).
% 24.46/16.15  tff(c_20840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19430, c_20838])).
% 24.46/16.15  tff(c_20841, plain, (![C_70]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', C_70)) | r1_tarski('#skF_4', C_70))), inference(splitRight, [status(thm)], [c_802])).
% 24.46/16.15  tff(c_33336, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_33208, c_20841])).
% 24.46/16.15  tff(c_33343, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_33336, c_6])).
% 24.46/16.15  tff(c_33349, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_467, c_33343])).
% 24.46/16.15  tff(c_33274, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_33187, c_2017])).
% 24.46/16.15  tff(c_37237, plain, (r1_tarski('#skF_2', '#skF_4') | '#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_33274, c_798])).
% 24.46/16.15  tff(c_37246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_468, c_33349, c_37237])).
% 24.46/16.15  tff(c_37248, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_455])).
% 24.46/16.15  tff(c_26, plain, (![C_20, A_18, B_19]: (k2_xboole_0(k2_zfmisc_1(C_20, A_18), k2_zfmisc_1(C_20, B_19))=k2_zfmisc_1(C_20, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.46/16.15  tff(c_37909, plain, (![A_467, C_468, B_469]: (k2_xboole_0(k2_zfmisc_1(A_467, C_468), k2_zfmisc_1(B_469, C_468))=k2_zfmisc_1(k2_xboole_0(A_467, B_469), C_468))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.46/16.15  tff(c_38637, plain, (![A_484]: (k2_xboole_0(k2_zfmisc_1(A_484, '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1(k2_xboole_0(A_484, '#skF_3'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_37909])).
% 24.46/16.15  tff(c_38701, plain, (k2_zfmisc_1(k2_xboole_0('#skF_1', '#skF_3'), '#skF_4')=k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_38637])).
% 24.46/16.15  tff(c_133, plain, (![A_37, B_36]: (r1_tarski(A_37, k2_xboole_0(B_36, A_37)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_18])).
% 24.46/16.15  tff(c_183, plain, (![A_37, B_36]: (k2_xboole_0(A_37, k2_xboole_0(B_36, A_37))=k2_xboole_0(B_36, A_37))), inference(resolution, [status(thm)], [c_133, c_167])).
% 24.46/16.15  tff(c_40523, plain, (![B_515]: (k2_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(B_515, '#skF_4'))=k2_zfmisc_1(k2_xboole_0('#skF_3', B_515), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_37909])).
% 24.46/16.15  tff(c_52699, plain, (![B_645]: (k3_xboole_0(k2_zfmisc_1(B_645, '#skF_4'), k2_zfmisc_1(k2_xboole_0('#skF_3', B_645), '#skF_4'))=k2_zfmisc_1(B_645, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_40523, c_127])).
% 24.46/16.15  tff(c_52862, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_4', '#skF_2')), k2_zfmisc_1(k2_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_3')), '#skF_4'))=k2_zfmisc_1(k2_xboole_0('#skF_1', '#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38701, c_52699])).
% 24.46/16.15  tff(c_52970, plain, (k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38701, c_16, c_16, c_4, c_28, c_183, c_52862])).
% 24.46/16.15  tff(c_37249, plain, (![C_445, A_446, B_447]: (k2_xboole_0(k2_zfmisc_1(C_445, A_446), k2_zfmisc_1(C_445, B_447))=k2_zfmisc_1(C_445, k2_xboole_0(A_446, B_447)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.46/16.15  tff(c_37262, plain, (![C_445, B_447, A_446]: (r1_tarski(k2_zfmisc_1(C_445, B_447), k2_zfmisc_1(C_445, k2_xboole_0(A_446, B_447))))), inference(superposition, [status(thm), theory('equality')], [c_37249, c_133])).
% 24.46/16.15  tff(c_53050, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_52970, c_37262])).
% 24.46/16.15  tff(c_452, plain, (![C_56]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(C_56, '#skF_4')) | r1_tarski('#skF_3', C_56) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_449])).
% 24.46/16.15  tff(c_37351, plain, (![C_56]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(C_56, '#skF_4')) | r1_tarski('#skF_3', C_56))), inference(negUnitSimplification, [status(thm)], [c_37248, c_452])).
% 24.46/16.15  tff(c_53115, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_53050, c_37351])).
% 24.46/16.15  tff(c_53119, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_53115, c_6])).
% 24.46/16.15  tff(c_53125, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_39, c_53119])).
% 24.46/16.15  tff(c_37363, plain, (![A_451, B_452, C_453]: (~r1_tarski(k2_zfmisc_1(A_451, B_452), k2_zfmisc_1(A_451, C_453)) | r1_tarski(B_452, C_453) | k1_xboole_0=A_451)), inference(cnfTransformation, [status(thm)], [f_56])).
% 24.46/16.15  tff(c_37369, plain, (![B_452]: (~r1_tarski(k2_zfmisc_1('#skF_3', B_452), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_452, '#skF_4') | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_37363])).
% 24.46/16.15  tff(c_38226, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_37369])).
% 24.46/16.15  tff(c_38230, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38226, c_32])).
% 24.46/16.15  tff(c_53126, plain, (k2_xboole_0('#skF_3', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_53115, c_12])).
% 24.46/16.15  tff(c_38236, plain, (![B_474, A_475]: (k3_xboole_0(k2_xboole_0(B_474, A_475), A_475)=A_475)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_38187])).
% 24.46/16.15  tff(c_38314, plain, (![B_2, A_1]: (k3_xboole_0(k2_xboole_0(B_2, A_1), B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_38236])).
% 24.46/16.15  tff(c_53234, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_53126, c_38314])).
% 24.46/16.15  tff(c_38221, plain, (![B_36, A_37]: (k3_xboole_0(k2_xboole_0(B_36, A_37), A_37)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_38187])).
% 24.46/16.15  tff(c_38470, plain, (![A_478, C_479, B_480, D_481]: (k3_xboole_0(k2_zfmisc_1(A_478, C_479), k2_zfmisc_1(B_480, D_481))=k2_zfmisc_1(k3_xboole_0(A_478, B_480), k3_xboole_0(C_479, D_481)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 24.46/16.15  tff(c_38510, plain, (![A_478, B_480, C_479, D_481]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_478, B_480), k3_xboole_0(C_479, D_481)), k2_zfmisc_1(A_478, C_479)))), inference(superposition, [status(thm), theory('equality')], [c_38470, c_14])).
% 24.46/16.15  tff(c_56244, plain, (![C_658, D_659]: (r1_tarski(k2_zfmisc_1('#skF_3', k3_xboole_0(C_658, D_659)), k2_zfmisc_1('#skF_1', C_658)))), inference(superposition, [status(thm), theory('equality')], [c_53234, c_38510])).
% 24.46/16.15  tff(c_65175, plain, (![A_746, B_747]: (r1_tarski(k2_zfmisc_1('#skF_3', A_746), k2_zfmisc_1('#skF_1', k2_xboole_0(B_747, A_746))))), inference(superposition, [status(thm), theory('equality')], [c_38221, c_56244])).
% 24.46/16.15  tff(c_65551, plain, (![B_750]: (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', k2_xboole_0(B_750, '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_65175])).
% 24.46/16.15  tff(c_38227, plain, (![A_15, B_16, C_17]: (~r1_tarski(k2_zfmisc_1(A_15, B_16), k2_zfmisc_1(A_15, C_17)) | r1_tarski(B_16, C_17) | A_15='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38226, c_20])).
% 24.46/16.15  tff(c_65554, plain, (![B_750]: (r1_tarski('#skF_2', k2_xboole_0(B_750, '#skF_4')) | '#skF_3'='#skF_1')), inference(resolution, [status(thm)], [c_65551, c_38227])).
% 24.46/16.15  tff(c_65617, plain, (![B_751]: (r1_tarski('#skF_2', k2_xboole_0(B_751, '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_39, c_65554])).
% 24.46/16.15  tff(c_65729, plain, (![B_753]: (k2_xboole_0('#skF_2', k2_xboole_0(B_753, '#skF_4'))=k2_xboole_0(B_753, '#skF_4'))), inference(resolution, [status(thm)], [c_65617, c_12])).
% 24.46/16.15  tff(c_65890, plain, (![B_753]: (k3_xboole_0('#skF_2', k2_xboole_0(B_753, '#skF_4'))='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_65729, c_16])).
% 24.46/16.15  tff(c_38520, plain, (![B_480, D_481]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(B_480, D_481))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_480), k3_xboole_0('#skF_4', D_481)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_38470])).
% 24.46/16.15  tff(c_45530, plain, (![B_595, D_596]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_595), k3_xboole_0('#skF_4', D_596))=k2_zfmisc_1(k3_xboole_0('#skF_1', B_595), k3_xboole_0('#skF_2', D_596)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38520])).
% 24.46/16.15  tff(c_45672, plain, (![B_595, B_36]: (k2_zfmisc_1(k3_xboole_0('#skF_1', B_595), k3_xboole_0('#skF_2', k2_xboole_0(B_36, '#skF_4')))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_595), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_45530])).
% 24.46/16.15  tff(c_72244, plain, (![B_785]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_785), '#skF_4')=k2_zfmisc_1(k3_xboole_0('#skF_1', B_785), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65890, c_45672])).
% 24.46/16.15  tff(c_72454, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_197, c_72244])).
% 24.46/16.15  tff(c_72497, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53234, c_36, c_72454])).
% 24.46/16.15  tff(c_38229, plain, (![B_16, A_15, C_17]: (~r1_tarski(k2_zfmisc_1(B_16, A_15), k2_zfmisc_1(C_17, A_15)) | r1_tarski(B_16, C_17) | A_15='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38226, c_22])).
% 24.46/16.15  tff(c_72567, plain, (![B_16]: (~r1_tarski(k2_zfmisc_1(B_16, '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_16, '#skF_3') | '#skF_2'='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_72497, c_38229])).
% 24.46/16.15  tff(c_75450, plain, (![B_799]: (~r1_tarski(k2_zfmisc_1(B_799, '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_799, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38230, c_72567])).
% 24.46/16.15  tff(c_75491, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_75450])).
% 24.46/16.15  tff(c_75505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53125, c_75491])).
% 24.46/16.15  tff(c_75507, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_37369])).
% 24.46/16.15  tff(c_37366, plain, (![C_453]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', C_453)) | r1_tarski('#skF_4', C_453) | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_37363])).
% 24.46/16.15  tff(c_78025, plain, (![C_453]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', C_453)) | r1_tarski('#skF_4', C_453))), inference(negUnitSimplification, [status(thm)], [c_75507, c_37366])).
% 24.46/16.15  tff(c_95617, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_95587, c_78025])).
% 24.46/16.15  tff(c_95638, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_95617, c_6])).
% 24.46/16.15  tff(c_97662, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_95638])).
% 24.46/16.15  tff(c_85987, plain, (![B_939, D_940]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_939), k3_xboole_0('#skF_4', D_940))=k2_zfmisc_1(k3_xboole_0('#skF_1', B_939), k3_xboole_0('#skF_2', D_940)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_75887])).
% 24.46/16.15  tff(c_106254, plain, (![B_1089, D_1090]: (k2_zfmisc_1(k3_xboole_0('#skF_1', k2_xboole_0(B_1089, '#skF_3')), k3_xboole_0('#skF_2', D_1090))=k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', D_1090)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_85987])).
% 24.46/16.15  tff(c_78739, plain, (![A_862, B_863, A_3, B_4]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_862, B_863), k3_xboole_0(A_3, B_4)), k2_zfmisc_1(A_862, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_78641])).
% 24.46/16.15  tff(c_110839, plain, (![D_1109]: (r1_tarski(k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', D_1109)), k2_zfmisc_1('#skF_1', D_1109)))), inference(superposition, [status(thm), theory('equality')], [c_106254, c_78739])).
% 24.46/16.15  tff(c_110905, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_197, c_110839])).
% 24.46/16.15  tff(c_110926, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_110905])).
% 24.46/16.15  tff(c_111252, plain, (r1_tarski('#skF_2', '#skF_4') | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_110926, c_20])).
% 24.46/16.15  tff(c_111264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_97662, c_111252])).
% 24.46/16.15  tff(c_111265, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_95638])).
% 24.46/16.15  tff(c_78904, plain, (![A_869, B_870, A_871]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_869, B_870), A_871), k2_zfmisc_1(A_869, A_871)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_78641])).
% 24.46/16.15  tff(c_79337, plain, (![B_880, A_881, A_882]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(B_880, A_881), A_882), k2_zfmisc_1(A_881, A_882)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_78904])).
% 24.46/16.15  tff(c_79387, plain, (![B_880]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(B_880, '#skF_3'), '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_79337])).
% 24.46/16.15  tff(c_113643, plain, (![B_1142]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(B_1142, '#skF_3'), '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_111265, c_79387])).
% 24.46/16.15  tff(c_113646, plain, (![B_1142]: (r1_tarski(k3_xboole_0(B_1142, '#skF_3'), '#skF_1') | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_113643, c_22])).
% 24.46/16.15  tff(c_113709, plain, (![B_1143]: (r1_tarski(k3_xboole_0(B_1143, '#skF_3'), '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_37248, c_113646])).
% 24.46/16.15  tff(c_113728, plain, (r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_75586, c_113709])).
% 24.46/16.15  tff(c_113759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95631, c_113728])).
% 24.46/16.15  tff(c_113760, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 24.46/16.15  tff(c_113761, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_30])).
% 24.46/16.15  tff(c_113768, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113761, c_36])).
% 24.46/16.15  tff(c_114327, plain, (![A_1178, B_1179, C_1180]: (~r1_tarski(k2_zfmisc_1(A_1178, B_1179), k2_zfmisc_1(A_1178, C_1180)) | r1_tarski(B_1179, C_1180) | k1_xboole_0=A_1178)), inference(cnfTransformation, [status(thm)], [f_56])).
% 24.46/16.15  tff(c_114336, plain, (![C_1180]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_1', C_1180)) | r1_tarski('#skF_2', C_1180) | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_113768, c_114327])).
% 24.46/16.15  tff(c_114439, plain, (![C_1183]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_1', C_1183)) | r1_tarski('#skF_2', C_1183))), inference(negUnitSimplification, [status(thm)], [c_34, c_114336])).
% 24.46/16.15  tff(c_114458, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_114439])).
% 24.46/16.15  tff(c_114460, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_114458, c_6])).
% 24.46/16.15  tff(c_114466, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_113760, c_114460])).
% 24.46/16.15  tff(c_114339, plain, (![B_1179]: (~r1_tarski(k2_zfmisc_1('#skF_1', B_1179), k2_zfmisc_1('#skF_1', '#skF_4')) | r1_tarski(B_1179, '#skF_2') | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_113768, c_114327])).
% 24.46/16.15  tff(c_114643, plain, (![B_1187]: (~r1_tarski(k2_zfmisc_1('#skF_1', B_1187), k2_zfmisc_1('#skF_1', '#skF_4')) | r1_tarski(B_1187, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_114339])).
% 24.46/16.15  tff(c_114653, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_114643])).
% 24.46/16.15  tff(c_114659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114466, c_114653])).
% 24.46/16.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.46/16.15  
% 24.46/16.15  Inference rules
% 24.46/16.15  ----------------------
% 24.46/16.15  #Ref     : 0
% 24.46/16.15  #Sup     : 29160
% 24.46/16.15  #Fact    : 0
% 24.46/16.15  #Define  : 0
% 24.46/16.15  #Split   : 6
% 24.46/16.15  #Chain   : 0
% 24.46/16.15  #Close   : 0
% 24.46/16.15  
% 24.46/16.15  Ordering : KBO
% 24.46/16.15  
% 24.46/16.15  Simplification rules
% 24.46/16.15  ----------------------
% 24.46/16.15  #Subsume      : 2177
% 24.46/16.15  #Demod        : 35359
% 24.46/16.15  #Tautology    : 16331
% 24.46/16.15  #SimpNegUnit  : 105
% 24.46/16.15  #BackRed      : 94
% 24.46/16.15  
% 24.46/16.15  #Partial instantiations: 0
% 24.46/16.15  #Strategies tried      : 1
% 24.46/16.15  
% 24.46/16.15  Timing (in seconds)
% 24.46/16.15  ----------------------
% 24.46/16.15  Preprocessing        : 0.36
% 24.46/16.15  Parsing              : 0.20
% 24.46/16.15  CNF conversion       : 0.02
% 24.46/16.16  Main loop            : 14.99
% 24.46/16.16  Inferencing          : 1.95
% 24.46/16.16  Reduction            : 9.60
% 24.46/16.16  Demodulation         : 8.80
% 24.46/16.16  BG Simplification    : 0.26
% 24.46/16.16  Subsumption          : 2.47
% 24.46/16.16  Abstraction          : 0.48
% 24.46/16.16  MUC search           : 0.00
% 24.46/16.16  Cooper               : 0.00
% 24.46/16.16  Total                : 15.42
% 24.46/16.16  Index Insertion      : 0.00
% 24.46/16.16  Index Deletion       : 0.00
% 24.46/16.16  Index Matching       : 0.00
% 24.46/16.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
