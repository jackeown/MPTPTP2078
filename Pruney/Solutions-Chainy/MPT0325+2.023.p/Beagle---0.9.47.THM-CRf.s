%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:23 EST 2020

% Result     : Theorem 29.53s
% Output     : CNFRefutation 29.53s
% Verified   : 
% Statistics : Number of formulae       :  173 (5046 expanded)
%              Number of leaves         :   18 (1674 expanded)
%              Depth                    :   20
%              Number of atoms          :  247 (8754 expanded)
%              Number of equality atoms :  208 (6972 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_87,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_10,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_98,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_98])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_694,plain,(
    ! [A_51,C_52,B_53,D_54] : k3_xboole_0(k2_zfmisc_1(A_51,C_52),k2_zfmisc_1(B_53,D_54)) = k2_zfmisc_1(k3_xboole_0(A_51,B_53),k3_xboole_0(C_52,D_54)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_769,plain,(
    ! [A_51,A_7,C_52] : k2_zfmisc_1(k3_xboole_0(A_51,A_7),k3_xboole_0(C_52,k1_xboole_0)) = k3_xboole_0(k2_zfmisc_1(A_51,C_52),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_694])).

tff(c_1374,plain,(
    ! [A_67,A_68,C_69] : k2_zfmisc_1(k3_xboole_0(A_67,A_68),k3_xboole_0(C_69,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_67,C_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_769])).

tff(c_2349,plain,(
    ! [C_92] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_92)) = k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k3_xboole_0(C_92,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1374])).

tff(c_2443,plain,(
    k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2349])).

tff(c_715,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_108])).

tff(c_775,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_715])).

tff(c_16,plain,(
    ! [D_16,B_14,A_13,C_15] :
      ( D_16 = B_14
      | k1_xboole_0 = B_14
      | k1_xboole_0 = A_13
      | k2_zfmisc_1(C_15,D_16) != k2_zfmisc_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_933,plain,(
    ! [B_14,A_13] :
      ( k3_xboole_0('#skF_4','#skF_2') = B_14
      | k1_xboole_0 = B_14
      | k1_xboole_0 = A_13
      | k2_zfmisc_1(A_13,B_14) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_16])).

tff(c_30100,plain,
    ( k3_xboole_0('#skF_4','#skF_2') = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_933])).

tff(c_30134,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_30100])).

tff(c_22,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14,D_16] :
      ( C_15 = A_13
      | k1_xboole_0 = B_14
      | k1_xboole_0 = A_13
      | k2_zfmisc_1(C_15,D_16) != k2_zfmisc_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2506,plain,(
    ! [C_15,D_16] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_15
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_15,D_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2443,c_18])).

tff(c_2516,plain,(
    ! [C_15,D_16] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_15
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_15,D_16) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_2506])).

tff(c_2931,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2516])).

tff(c_12,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_760,plain,(
    ! [B_53,B_8,D_54] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_53),k3_xboole_0(B_8,D_54)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_53,D_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_694])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1076,plain,(
    ! [A_59,B_60,C_61,D_62] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_59,B_60),k3_xboole_0(C_61,D_62)),k2_zfmisc_1(A_59,C_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_4])).

tff(c_4343,plain,(
    ! [B_107,A_108,C_109,D_110] : r1_tarski(k2_zfmisc_1(k3_xboole_0(B_107,A_108),k3_xboole_0(C_109,D_110)),k2_zfmisc_1(A_108,C_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1076])).

tff(c_4549,plain,(
    ! [B_111,D_112,B_113] : r1_tarski(k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_111,D_112)),k2_zfmisc_1(B_111,B_113)) ),
    inference(superposition,[status(thm),theory(equality)],[c_760,c_4343])).

tff(c_4609,plain,(
    ! [A_7,B_113] : r1_tarski(k3_xboole_0(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(A_7,B_113)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_4549])).

tff(c_4622,plain,(
    ! [A_114,B_115] : r1_tarski(k1_xboole_0,k2_zfmisc_1(A_114,B_115)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2931,c_4609])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4642,plain,(
    ! [A_114,B_115] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_114,B_115)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4622,c_6])).

tff(c_1885,plain,(
    ! [A_83,B_84,D_85] : k2_zfmisc_1(k3_xboole_0(A_83,B_84),k3_xboole_0(k1_xboole_0,D_85)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_84,D_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_694])).

tff(c_1983,plain,(
    ! [D_85] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'),D_85)) = k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k3_xboole_0(k1_xboole_0,D_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1885])).

tff(c_5358,plain,(
    ! [D_129] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k3_xboole_0(k1_xboole_0,D_129)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4642,c_1983])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5414,plain,(
    ! [D_129] :
      ( k3_xboole_0(k1_xboole_0,D_129) = k1_xboole_0
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5358,c_8])).

tff(c_5474,plain,(
    ! [D_130] : k3_xboole_0(k1_xboole_0,D_130) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_5414])).

tff(c_48,plain,(
    ! [B_21,A_22] : k3_xboole_0(B_21,A_22) = k3_xboole_0(A_22,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_63,plain,(
    ! [B_21,A_22] : r1_tarski(k3_xboole_0(B_21,A_22),A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4])).

tff(c_5588,plain,(
    ! [D_130] : r1_tarski(k1_xboole_0,D_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_5474,c_63])).

tff(c_30142,plain,(
    ! [D_130] : r1_tarski('#skF_1',D_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30134,c_5588])).

tff(c_30156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30142,c_87])).

tff(c_30158,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30100])).

tff(c_939,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0('#skF_1','#skF_3') = A_13
      | k1_xboole_0 = B_14
      | k1_xboole_0 = A_13
      | k2_zfmisc_1(A_13,B_14) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_18])).

tff(c_43535,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_939])).

tff(c_43536,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_30158,c_43535])).

tff(c_43581,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_43536])).

tff(c_43599,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43581,c_43581,c_10])).

tff(c_43600,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43581,c_22])).

tff(c_43733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43599,c_43600])).

tff(c_43734,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_43536])).

tff(c_44255,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_43734,c_63])).

tff(c_44352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_44255])).

tff(c_44354,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2516])).

tff(c_763,plain,(
    ! [A_51,C_52,B_8] : k2_zfmisc_1(k3_xboole_0(A_51,k1_xboole_0),k3_xboole_0(C_52,B_8)) = k3_xboole_0(k2_zfmisc_1(A_51,C_52),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_694])).

tff(c_1716,plain,(
    ! [A_79,C_80,B_81] : k2_zfmisc_1(k3_xboole_0(A_79,k1_xboole_0),k3_xboole_0(C_80,B_81)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_79,C_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_763])).

tff(c_2088,plain,(
    ! [A_88] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_88,k2_zfmisc_1('#skF_1','#skF_2'))) = k2_zfmisc_1(k3_xboole_0(A_88,k1_xboole_0),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1716])).

tff(c_2172,plain,(
    k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k1_xboole_0),k2_zfmisc_1('#skF_1','#skF_2')) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2088])).

tff(c_44390,plain,(
    ! [D_16,C_15] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = D_16
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_15,D_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2172,c_16])).

tff(c_44410,plain,(
    ! [D_404,C_405] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = D_404
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_405,D_404) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44354,c_22,c_44390])).

tff(c_44440,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2443,c_44410])).

tff(c_44396,plain,(
    ! [C_15,D_16] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = C_15
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_15,D_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2172,c_18])).

tff(c_44406,plain,(
    ! [C_15,D_16] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = C_15
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_15,D_16) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44354,c_22,c_44396])).

tff(c_44809,plain,(
    ! [C_15,D_16] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_15
      | k2_zfmisc_1(C_15,D_16) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44440,c_44440,c_44406])).

tff(c_44812,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_44809])).

tff(c_44856,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44812,c_22])).

tff(c_44841,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44812,c_44440])).

tff(c_2500,plain,(
    ! [D_16,C_15] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = D_16
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_15,D_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2443,c_16])).

tff(c_2515,plain,(
    ! [D_16,C_15] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = D_16
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_15,D_16) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_2500])).

tff(c_45468,plain,(
    ! [D_16,C_15] :
      ( D_16 = '#skF_1'
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_15,D_16) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44841,c_44841,c_44841,c_2515])).

tff(c_45470,plain,(
    ! [D_412,C_413] :
      ( D_412 = '#skF_1'
      | k2_zfmisc_1(C_413,D_412) != '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_44856,c_45468])).

tff(c_45492,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_44812,c_45470])).

tff(c_45494,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45492,c_44812])).

tff(c_44813,plain,(
    ! [C_406,D_407] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_406
      | k2_zfmisc_1(C_406,D_407) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44440,c_44440,c_44406])).

tff(c_44835,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_44813])).

tff(c_45829,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45494,c_45492,c_44835])).

tff(c_45905,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_45829,c_63])).

tff(c_45926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_45905])).

tff(c_45927,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_45928,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_45939,plain,(
    ! [A_422,B_423] :
      ( k3_xboole_0(A_422,B_423) = A_422
      | ~ r1_tarski(A_422,B_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45954,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_45928,c_45939])).

tff(c_45962,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45954,c_4])).

tff(c_45970,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_45962,c_6])).

tff(c_46978,plain,(
    ! [A_452,C_453,B_454,D_455] : k3_xboole_0(k2_zfmisc_1(A_452,C_453),k2_zfmisc_1(B_454,D_455)) = k2_zfmisc_1(k3_xboole_0(A_452,B_454),k3_xboole_0(C_453,D_455)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48586,plain,(
    ! [B_492,D_493,A_494,C_495] : k3_xboole_0(k2_zfmisc_1(B_492,D_493),k2_zfmisc_1(A_494,C_495)) = k2_zfmisc_1(k3_xboole_0(A_494,B_492),k3_xboole_0(C_495,D_493)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46978,c_2])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10,D_12] : k3_xboole_0(k2_zfmisc_1(A_9,C_11),k2_zfmisc_1(B_10,D_12)) = k2_zfmisc_1(k3_xboole_0(A_9,B_10),k3_xboole_0(C_11,D_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_61783,plain,(
    ! [B_661,A_662,D_663,C_664] : k2_zfmisc_1(k3_xboole_0(B_661,A_662),k3_xboole_0(D_663,C_664)) = k2_zfmisc_1(k3_xboole_0(A_662,B_661),k3_xboole_0(C_664,D_663)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48586,c_14])).

tff(c_62179,plain,(
    ! [A_662,B_661] : k2_zfmisc_1(k3_xboole_0(A_662,B_661),k3_xboole_0('#skF_1','#skF_1')) = k2_zfmisc_1(k3_xboole_0(B_661,A_662),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45970,c_61783])).

tff(c_62611,plain,(
    ! [B_667,A_668] : k2_zfmisc_1(k3_xboole_0(B_667,A_668),'#skF_1') = k2_zfmisc_1(k3_xboole_0(A_668,B_667),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45970,c_62179])).

tff(c_62752,plain,(
    ! [A_668,B_667] :
      ( k1_xboole_0 = '#skF_1'
      | k3_xboole_0(A_668,B_667) = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0(B_667,A_668),'#skF_1') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62611,c_8])).

tff(c_74712,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_62752])).

tff(c_74719,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74712,c_74712,c_12])).

tff(c_74721,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74712,c_22])).

tff(c_76837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74719,c_74721])).

tff(c_76839,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_62752])).

tff(c_45953,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_45939])).

tff(c_47011,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_46978,c_45953])).

tff(c_47070,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45954,c_2,c_47011])).

tff(c_47088,plain,(
    ! [B_14,A_13] :
      ( k3_xboole_0('#skF_4','#skF_2') = B_14
      | k1_xboole_0 = B_14
      | k1_xboole_0 = A_13
      | k2_zfmisc_1(A_13,B_14) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47070,c_16])).

tff(c_94839,plain,
    ( k3_xboole_0('#skF_4','#skF_2') = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_47088])).

tff(c_94840,plain,
    ( k3_xboole_0('#skF_4','#skF_2') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_76839,c_94839])).

tff(c_94894,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_94840])).

tff(c_45955,plain,(
    ! [A_3,B_4] : k3_xboole_0(k3_xboole_0(A_3,B_4),A_3) = k3_xboole_0(A_3,B_4) ),
    inference(resolution,[status(thm)],[c_4,c_45939])).

tff(c_47474,plain,(
    ! [B_464,B_465,D_466] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_464),k3_xboole_0(B_465,D_466)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_464,D_466)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_46978])).

tff(c_53037,plain,(
    ! [B_585,A_586,B_587] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_585),k3_xboole_0(A_586,B_587)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_585,A_586)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45955,c_47474])).

tff(c_47059,plain,(
    ! [A_452,A_7,C_453] : k2_zfmisc_1(k3_xboole_0(A_452,A_7),k3_xboole_0(C_453,k1_xboole_0)) = k3_xboole_0(k2_zfmisc_1(A_452,C_453),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_46978])).

tff(c_47078,plain,(
    ! [A_452,A_7,C_453] : k2_zfmisc_1(k3_xboole_0(A_452,A_7),k3_xboole_0(C_453,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_452,C_453)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_47059])).

tff(c_53096,plain,(
    ! [A_586,B_585] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,A_586)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_585,A_586)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53037,c_47078])).

tff(c_53275,plain,(
    ! [B_585,A_586] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_585,A_586)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_53096])).

tff(c_47053,plain,(
    ! [A_452,C_453,B_8] : k2_zfmisc_1(k3_xboole_0(A_452,k1_xboole_0),k3_xboole_0(C_453,B_8)) = k3_xboole_0(k2_zfmisc_1(A_452,C_453),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_46978])).

tff(c_48067,plain,(
    ! [A_480,C_481,B_482] : k2_zfmisc_1(k3_xboole_0(A_480,k1_xboole_0),k3_xboole_0(C_481,B_482)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_480,C_481)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_47053])).

tff(c_48161,plain,(
    ! [A_480] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_480,k2_zfmisc_1('#skF_1','#skF_2'))) = k2_zfmisc_1(k3_xboole_0(A_480,k1_xboole_0),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45953,c_48067])).

tff(c_53543,plain,(
    ! [A_590] : k2_zfmisc_1(k3_xboole_0(A_590,k1_xboole_0),k2_zfmisc_1('#skF_1','#skF_2')) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53275,c_48161])).

tff(c_53621,plain,(
    ! [A_590] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(A_590,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53543,c_8])).

tff(c_53661,plain,(
    ! [A_590] :
      ( k3_xboole_0(A_590,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_53621])).

tff(c_54589,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_53661])).

tff(c_47744,plain,(
    ! [A_471,B_472,D_473] : k2_zfmisc_1(k3_xboole_0(A_471,B_472),k3_xboole_0(k1_xboole_0,D_473)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_472,D_473)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_46978])).

tff(c_47843,plain,(
    ! [D_473] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1('#skF_3',D_473)) = k2_zfmisc_1('#skF_1',k3_xboole_0(k1_xboole_0,D_473)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45954,c_47744])).

tff(c_53312,plain,(
    ! [D_473] : k2_zfmisc_1('#skF_1',k3_xboole_0(k1_xboole_0,D_473)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53275,c_47843])).

tff(c_53618,plain,(
    ! [A_590,C_15,D_16] :
      ( k3_xboole_0(A_590,k1_xboole_0) = C_15
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(A_590,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_15,D_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53543,c_18])).

tff(c_54932,plain,(
    ! [A_606,C_607,D_608] :
      ( k3_xboole_0(A_606,k1_xboole_0) = C_607
      | k3_xboole_0(A_606,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_607,D_608) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_53618])).

tff(c_54969,plain,(
    ! [A_609] :
      ( k3_xboole_0(A_609,k1_xboole_0) = '#skF_1'
      | k3_xboole_0(A_609,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53312,c_54932])).

tff(c_48397,plain,(
    ! [A_488,A_489,C_490] : k2_zfmisc_1(k3_xboole_0(A_488,A_489),k3_xboole_0(C_490,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_488,C_490)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_47059])).

tff(c_48522,plain,(
    ! [A_1,B_2,C_490] : k2_zfmisc_1(k3_xboole_0(A_1,B_2),k3_xboole_0(C_490,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_2,C_490)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_48397])).

tff(c_54761,plain,(
    ! [A_1,B_2,C_490] : k2_zfmisc_1(k3_xboole_0(A_1,B_2),k3_xboole_0(C_490,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53275,c_48522])).

tff(c_54977,plain,(
    ! [C_490,A_609] :
      ( k2_zfmisc_1(k1_xboole_0,k3_xboole_0(C_490,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k1_xboole_0)
      | k3_xboole_0(A_609,k1_xboole_0) = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54969,c_54761])).

tff(c_55192,plain,(
    ! [A_609] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(A_609,k1_xboole_0) = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_54977])).

tff(c_55274,plain,(
    ! [A_610] : k3_xboole_0(A_610,k1_xboole_0) = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54589,c_55192])).

tff(c_55418,plain,(
    ! [A_610] : r1_tarski('#skF_1',A_610) ),
    inference(superposition,[status(thm),theory(equality)],[c_55274,c_4])).

tff(c_55406,plain,(
    ! [B_4] : k3_xboole_0(k1_xboole_0,B_4) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_55274,c_45955])).

tff(c_47846,plain,(
    ! [B_2,A_1,D_473] : k2_zfmisc_1(k3_xboole_0(B_2,A_1),k3_xboole_0(k1_xboole_0,D_473)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_2,D_473)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_47744])).

tff(c_56273,plain,(
    ! [B_621,A_622] : k2_zfmisc_1(k3_xboole_0(B_621,A_622),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55406,c_55406,c_47846])).

tff(c_55193,plain,(
    ! [A_609] : k3_xboole_0(A_609,k1_xboole_0) = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54589,c_55192])).

tff(c_55263,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55193,c_54589])).

tff(c_53660,plain,(
    ! [A_590,C_15,D_16] :
      ( k3_xboole_0(A_590,k1_xboole_0) = C_15
      | k3_xboole_0(A_590,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_15,D_16) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_53618])).

tff(c_55260,plain,(
    ! [C_15,D_16] :
      ( C_15 = '#skF_1'
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_15,D_16) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55193,c_55193,c_55193,c_53660])).

tff(c_56013,plain,(
    ! [C_15,D_16] :
      ( C_15 = '#skF_1'
      | k2_zfmisc_1(C_15,D_16) != '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_55263,c_55260])).

tff(c_56359,plain,(
    ! [B_621,A_622] : k3_xboole_0(B_621,A_622) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_56273,c_56013])).

tff(c_56940,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56359,c_45953])).

tff(c_56347,plain,(
    k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_45953,c_56273])).

tff(c_56431,plain,(
    ! [D_16,C_15] :
      ( D_16 = '#skF_1'
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k2_zfmisc_1(C_15,D_16) != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56347,c_16])).

tff(c_56446,plain,(
    ! [D_16,C_15] :
      ( D_16 = '#skF_1'
      | k2_zfmisc_1(C_15,D_16) != '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_55263,c_56431])).

tff(c_57020,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_56940,c_56446])).

tff(c_57029,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57020,c_45927])).

tff(c_57033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55418,c_57029])).

tff(c_57050,plain,(
    ! [A_629] : k3_xboole_0(A_629,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_53661])).

tff(c_57194,plain,(
    ! [A_629] : r1_tarski(k1_xboole_0,A_629) ),
    inference(superposition,[status(thm),theory(equality)],[c_57050,c_4])).

tff(c_94919,plain,(
    ! [A_629] : r1_tarski('#skF_2',A_629) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94894,c_57194])).

tff(c_94933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94919,c_45927])).

tff(c_94934,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_94840])).

tff(c_95550,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_94934,c_4])).

tff(c_95675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45927,c_95550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:41:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.53/17.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.53/17.26  
% 29.53/17.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.53/17.27  %$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 29.53/17.27  
% 29.53/17.27  %Foreground sorts:
% 29.53/17.27  
% 29.53/17.27  
% 29.53/17.27  %Background operators:
% 29.53/17.27  
% 29.53/17.27  
% 29.53/17.27  %Foreground operators:
% 29.53/17.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.53/17.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.53/17.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.53/17.27  tff('#skF_2', type, '#skF_2': $i).
% 29.53/17.27  tff('#skF_3', type, '#skF_3': $i).
% 29.53/17.27  tff('#skF_1', type, '#skF_1': $i).
% 29.53/17.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.53/17.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 29.53/17.27  tff('#skF_4', type, '#skF_4': $i).
% 29.53/17.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.53/17.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.53/17.27  
% 29.53/17.29  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 29.53/17.29  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 29.53/17.29  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 29.53/17.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 29.53/17.29  tff(f_41, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 29.53/17.29  tff(f_51, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 29.53/17.29  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 29.53/17.29  tff(c_20, plain, (~r1_tarski('#skF_2', '#skF_4') | ~r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 29.53/17.29  tff(c_87, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_20])).
% 29.53/17.29  tff(c_10, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.53/17.29  tff(c_24, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 29.53/17.29  tff(c_98, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.53/17.29  tff(c_108, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_98])).
% 29.53/17.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 29.53/17.29  tff(c_694, plain, (![A_51, C_52, B_53, D_54]: (k3_xboole_0(k2_zfmisc_1(A_51, C_52), k2_zfmisc_1(B_53, D_54))=k2_zfmisc_1(k3_xboole_0(A_51, B_53), k3_xboole_0(C_52, D_54)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 29.53/17.29  tff(c_769, plain, (![A_51, A_7, C_52]: (k2_zfmisc_1(k3_xboole_0(A_51, A_7), k3_xboole_0(C_52, k1_xboole_0))=k3_xboole_0(k2_zfmisc_1(A_51, C_52), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_694])).
% 29.53/17.29  tff(c_1374, plain, (![A_67, A_68, C_69]: (k2_zfmisc_1(k3_xboole_0(A_67, A_68), k3_xboole_0(C_69, k1_xboole_0))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_67, C_69)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_769])).
% 29.53/17.29  tff(c_2349, plain, (![C_92]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_92))=k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k3_xboole_0(C_92, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1374])).
% 29.53/17.29  tff(c_2443, plain, (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k3_xboole_0(k1_xboole_0, k1_xboole_0))=k3_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_2349])).
% 29.53/17.29  tff(c_715, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_694, c_108])).
% 29.53/17.29  tff(c_775, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_715])).
% 29.53/17.29  tff(c_16, plain, (![D_16, B_14, A_13, C_15]: (D_16=B_14 | k1_xboole_0=B_14 | k1_xboole_0=A_13 | k2_zfmisc_1(C_15, D_16)!=k2_zfmisc_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 29.53/17.29  tff(c_933, plain, (![B_14, A_13]: (k3_xboole_0('#skF_4', '#skF_2')=B_14 | k1_xboole_0=B_14 | k1_xboole_0=A_13 | k2_zfmisc_1(A_13, B_14)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_775, c_16])).
% 29.53/17.29  tff(c_30100, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_933])).
% 29.53/17.29  tff(c_30134, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_30100])).
% 29.53/17.29  tff(c_22, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 29.53/17.29  tff(c_18, plain, (![C_15, A_13, B_14, D_16]: (C_15=A_13 | k1_xboole_0=B_14 | k1_xboole_0=A_13 | k2_zfmisc_1(C_15, D_16)!=k2_zfmisc_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 29.53/17.29  tff(c_2506, plain, (![C_15, D_16]: (k2_zfmisc_1('#skF_1', '#skF_2')=C_15 | k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_zfmisc_1(C_15, D_16))), inference(superposition, [status(thm), theory('equality')], [c_2443, c_18])).
% 29.53/17.29  tff(c_2516, plain, (![C_15, D_16]: (k2_zfmisc_1('#skF_1', '#skF_2')=C_15 | k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_zfmisc_1(C_15, D_16))), inference(negUnitSimplification, [status(thm)], [c_22, c_2506])).
% 29.53/17.29  tff(c_2931, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2516])).
% 29.53/17.29  tff(c_12, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.53/17.29  tff(c_760, plain, (![B_53, B_8, D_54]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_53), k3_xboole_0(B_8, D_54))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_53, D_54)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_694])).
% 29.53/17.29  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 29.53/17.29  tff(c_1076, plain, (![A_59, B_60, C_61, D_62]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_59, B_60), k3_xboole_0(C_61, D_62)), k2_zfmisc_1(A_59, C_61)))), inference(superposition, [status(thm), theory('equality')], [c_694, c_4])).
% 29.53/17.29  tff(c_4343, plain, (![B_107, A_108, C_109, D_110]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(B_107, A_108), k3_xboole_0(C_109, D_110)), k2_zfmisc_1(A_108, C_109)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1076])).
% 29.53/17.29  tff(c_4549, plain, (![B_111, D_112, B_113]: (r1_tarski(k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_111, D_112)), k2_zfmisc_1(B_111, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_760, c_4343])).
% 29.53/17.29  tff(c_4609, plain, (![A_7, B_113]: (r1_tarski(k3_xboole_0(k1_xboole_0, k1_xboole_0), k2_zfmisc_1(A_7, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_4549])).
% 29.53/17.29  tff(c_4622, plain, (![A_114, B_115]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_114, B_115)))), inference(demodulation, [status(thm), theory('equality')], [c_2931, c_4609])).
% 29.53/17.29  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.53/17.29  tff(c_4642, plain, (![A_114, B_115]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_114, B_115))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4622, c_6])).
% 29.53/17.29  tff(c_1885, plain, (![A_83, B_84, D_85]: (k2_zfmisc_1(k3_xboole_0(A_83, B_84), k3_xboole_0(k1_xboole_0, D_85))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_84, D_85)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_694])).
% 29.53/17.29  tff(c_1983, plain, (![D_85]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'), D_85))=k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k3_xboole_0(k1_xboole_0, D_85)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1885])).
% 29.53/17.29  tff(c_5358, plain, (![D_129]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), k3_xboole_0(k1_xboole_0, D_129))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4642, c_1983])).
% 29.53/17.29  tff(c_8, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.53/17.29  tff(c_5414, plain, (![D_129]: (k3_xboole_0(k1_xboole_0, D_129)=k1_xboole_0 | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5358, c_8])).
% 29.53/17.29  tff(c_5474, plain, (![D_130]: (k3_xboole_0(k1_xboole_0, D_130)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_22, c_5414])).
% 29.53/17.29  tff(c_48, plain, (![B_21, A_22]: (k3_xboole_0(B_21, A_22)=k3_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_27])).
% 29.53/17.29  tff(c_63, plain, (![B_21, A_22]: (r1_tarski(k3_xboole_0(B_21, A_22), A_22))), inference(superposition, [status(thm), theory('equality')], [c_48, c_4])).
% 29.53/17.29  tff(c_5588, plain, (![D_130]: (r1_tarski(k1_xboole_0, D_130))), inference(superposition, [status(thm), theory('equality')], [c_5474, c_63])).
% 29.53/17.29  tff(c_30142, plain, (![D_130]: (r1_tarski('#skF_1', D_130))), inference(demodulation, [status(thm), theory('equality')], [c_30134, c_5588])).
% 29.53/17.29  tff(c_30156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30142, c_87])).
% 29.53/17.29  tff(c_30158, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_30100])).
% 29.53/17.29  tff(c_939, plain, (![A_13, B_14]: (k3_xboole_0('#skF_1', '#skF_3')=A_13 | k1_xboole_0=B_14 | k1_xboole_0=A_13 | k2_zfmisc_1(A_13, B_14)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_775, c_18])).
% 29.53/17.29  tff(c_43535, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_939])).
% 29.53/17.29  tff(c_43536, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_30158, c_43535])).
% 29.53/17.29  tff(c_43581, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_43536])).
% 29.53/17.29  tff(c_43599, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_43581, c_43581, c_10])).
% 29.53/17.29  tff(c_43600, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_43581, c_22])).
% 29.53/17.29  tff(c_43733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43599, c_43600])).
% 29.53/17.29  tff(c_43734, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_43536])).
% 29.53/17.29  tff(c_44255, plain, (r1_tarski('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_43734, c_63])).
% 29.53/17.29  tff(c_44352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_44255])).
% 29.53/17.29  tff(c_44354, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2516])).
% 29.53/17.29  tff(c_763, plain, (![A_51, C_52, B_8]: (k2_zfmisc_1(k3_xboole_0(A_51, k1_xboole_0), k3_xboole_0(C_52, B_8))=k3_xboole_0(k2_zfmisc_1(A_51, C_52), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_694])).
% 29.53/17.29  tff(c_1716, plain, (![A_79, C_80, B_81]: (k2_zfmisc_1(k3_xboole_0(A_79, k1_xboole_0), k3_xboole_0(C_80, B_81))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_79, C_80)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_763])).
% 29.53/17.29  tff(c_2088, plain, (![A_88]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_88, k2_zfmisc_1('#skF_1', '#skF_2')))=k2_zfmisc_1(k3_xboole_0(A_88, k1_xboole_0), k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1716])).
% 29.53/17.29  tff(c_2172, plain, (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, k1_xboole_0), k2_zfmisc_1('#skF_1', '#skF_2'))=k3_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_2088])).
% 29.53/17.29  tff(c_44390, plain, (![D_16, C_15]: (k2_zfmisc_1('#skF_1', '#skF_2')=D_16 | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_zfmisc_1(C_15, D_16))), inference(superposition, [status(thm), theory('equality')], [c_2172, c_16])).
% 29.53/17.29  tff(c_44410, plain, (![D_404, C_405]: (k2_zfmisc_1('#skF_1', '#skF_2')=D_404 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_zfmisc_1(C_405, D_404))), inference(negUnitSimplification, [status(thm)], [c_44354, c_22, c_44390])).
% 29.53/17.29  tff(c_44440, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2443, c_44410])).
% 29.53/17.29  tff(c_44396, plain, (![C_15, D_16]: (k3_xboole_0(k1_xboole_0, k1_xboole_0)=C_15 | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_zfmisc_1(C_15, D_16))), inference(superposition, [status(thm), theory('equality')], [c_2172, c_18])).
% 29.53/17.29  tff(c_44406, plain, (![C_15, D_16]: (k3_xboole_0(k1_xboole_0, k1_xboole_0)=C_15 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_zfmisc_1(C_15, D_16))), inference(negUnitSimplification, [status(thm)], [c_44354, c_22, c_44396])).
% 29.53/17.29  tff(c_44809, plain, (![C_15, D_16]: (k2_zfmisc_1('#skF_1', '#skF_2')=C_15 | k2_zfmisc_1(C_15, D_16)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44440, c_44440, c_44406])).
% 29.53/17.29  tff(c_44812, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_44809])).
% 29.53/17.29  tff(c_44856, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44812, c_22])).
% 29.53/17.29  tff(c_44841, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44812, c_44440])).
% 29.53/17.29  tff(c_2500, plain, (![D_16, C_15]: (k3_xboole_0(k1_xboole_0, k1_xboole_0)=D_16 | k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_zfmisc_1(C_15, D_16))), inference(superposition, [status(thm), theory('equality')], [c_2443, c_16])).
% 29.53/17.29  tff(c_2515, plain, (![D_16, C_15]: (k3_xboole_0(k1_xboole_0, k1_xboole_0)=D_16 | k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_zfmisc_1(C_15, D_16))), inference(negUnitSimplification, [status(thm)], [c_22, c_2500])).
% 29.53/17.29  tff(c_45468, plain, (![D_16, C_15]: (D_16='#skF_1' | k1_xboole_0='#skF_1' | k2_zfmisc_1(C_15, D_16)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44841, c_44841, c_44841, c_2515])).
% 29.53/17.29  tff(c_45470, plain, (![D_412, C_413]: (D_412='#skF_1' | k2_zfmisc_1(C_413, D_412)!='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44856, c_45468])).
% 29.53/17.29  tff(c_45492, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_44812, c_45470])).
% 29.53/17.29  tff(c_45494, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45492, c_44812])).
% 29.53/17.29  tff(c_44813, plain, (![C_406, D_407]: (k2_zfmisc_1('#skF_1', '#skF_2')=C_406 | k2_zfmisc_1(C_406, D_407)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44440, c_44440, c_44406])).
% 29.53/17.29  tff(c_44835, plain, (k3_xboole_0('#skF_1', '#skF_3')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_775, c_44813])).
% 29.53/17.29  tff(c_45829, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45494, c_45492, c_44835])).
% 29.53/17.29  tff(c_45905, plain, (r1_tarski('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_45829, c_63])).
% 29.53/17.29  tff(c_45926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_45905])).
% 29.53/17.29  tff(c_45927, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_20])).
% 29.53/17.29  tff(c_45928, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 29.53/17.29  tff(c_45939, plain, (![A_422, B_423]: (k3_xboole_0(A_422, B_423)=A_422 | ~r1_tarski(A_422, B_423))), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.53/17.29  tff(c_45954, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_45928, c_45939])).
% 29.53/17.29  tff(c_45962, plain, (r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45954, c_4])).
% 29.53/17.29  tff(c_45970, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_45962, c_6])).
% 29.53/17.29  tff(c_46978, plain, (![A_452, C_453, B_454, D_455]: (k3_xboole_0(k2_zfmisc_1(A_452, C_453), k2_zfmisc_1(B_454, D_455))=k2_zfmisc_1(k3_xboole_0(A_452, B_454), k3_xboole_0(C_453, D_455)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 29.53/17.29  tff(c_48586, plain, (![B_492, D_493, A_494, C_495]: (k3_xboole_0(k2_zfmisc_1(B_492, D_493), k2_zfmisc_1(A_494, C_495))=k2_zfmisc_1(k3_xboole_0(A_494, B_492), k3_xboole_0(C_495, D_493)))), inference(superposition, [status(thm), theory('equality')], [c_46978, c_2])).
% 29.53/17.29  tff(c_14, plain, (![A_9, C_11, B_10, D_12]: (k3_xboole_0(k2_zfmisc_1(A_9, C_11), k2_zfmisc_1(B_10, D_12))=k2_zfmisc_1(k3_xboole_0(A_9, B_10), k3_xboole_0(C_11, D_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 29.53/17.29  tff(c_61783, plain, (![B_661, A_662, D_663, C_664]: (k2_zfmisc_1(k3_xboole_0(B_661, A_662), k3_xboole_0(D_663, C_664))=k2_zfmisc_1(k3_xboole_0(A_662, B_661), k3_xboole_0(C_664, D_663)))), inference(superposition, [status(thm), theory('equality')], [c_48586, c_14])).
% 29.53/17.29  tff(c_62179, plain, (![A_662, B_661]: (k2_zfmisc_1(k3_xboole_0(A_662, B_661), k3_xboole_0('#skF_1', '#skF_1'))=k2_zfmisc_1(k3_xboole_0(B_661, A_662), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_45970, c_61783])).
% 29.53/17.29  tff(c_62611, plain, (![B_667, A_668]: (k2_zfmisc_1(k3_xboole_0(B_667, A_668), '#skF_1')=k2_zfmisc_1(k3_xboole_0(A_668, B_667), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_45970, c_62179])).
% 29.53/17.29  tff(c_62752, plain, (![A_668, B_667]: (k1_xboole_0='#skF_1' | k3_xboole_0(A_668, B_667)=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0(B_667, A_668), '#skF_1')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62611, c_8])).
% 29.53/17.29  tff(c_74712, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_62752])).
% 29.53/17.29  tff(c_74719, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74712, c_74712, c_12])).
% 29.53/17.29  tff(c_74721, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74712, c_22])).
% 29.53/17.29  tff(c_76837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74719, c_74721])).
% 29.53/17.29  tff(c_76839, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_62752])).
% 29.53/17.29  tff(c_45953, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_45939])).
% 29.53/17.29  tff(c_47011, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46978, c_45953])).
% 29.53/17.29  tff(c_47070, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_45954, c_2, c_47011])).
% 29.53/17.29  tff(c_47088, plain, (![B_14, A_13]: (k3_xboole_0('#skF_4', '#skF_2')=B_14 | k1_xboole_0=B_14 | k1_xboole_0=A_13 | k2_zfmisc_1(A_13, B_14)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_47070, c_16])).
% 29.53/17.29  tff(c_94839, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_47088])).
% 29.53/17.29  tff(c_94840, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_2' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_76839, c_94839])).
% 29.53/17.29  tff(c_94894, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_94840])).
% 29.53/17.29  tff(c_45955, plain, (![A_3, B_4]: (k3_xboole_0(k3_xboole_0(A_3, B_4), A_3)=k3_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_4, c_45939])).
% 29.53/17.29  tff(c_47474, plain, (![B_464, B_465, D_466]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_464), k3_xboole_0(B_465, D_466))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_464, D_466)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_46978])).
% 29.53/17.29  tff(c_53037, plain, (![B_585, A_586, B_587]: (k2_zfmisc_1(k3_xboole_0(k1_xboole_0, B_585), k3_xboole_0(A_586, B_587))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_585, A_586)))), inference(superposition, [status(thm), theory('equality')], [c_45955, c_47474])).
% 29.53/17.29  tff(c_47059, plain, (![A_452, A_7, C_453]: (k2_zfmisc_1(k3_xboole_0(A_452, A_7), k3_xboole_0(C_453, k1_xboole_0))=k3_xboole_0(k2_zfmisc_1(A_452, C_453), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_46978])).
% 29.53/17.29  tff(c_47078, plain, (![A_452, A_7, C_453]: (k2_zfmisc_1(k3_xboole_0(A_452, A_7), k3_xboole_0(C_453, k1_xboole_0))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_452, C_453)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_47059])).
% 29.53/17.29  tff(c_53096, plain, (![A_586, B_585]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(k1_xboole_0, A_586))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_585, A_586)))), inference(superposition, [status(thm), theory('equality')], [c_53037, c_47078])).
% 29.53/17.29  tff(c_53275, plain, (![B_585, A_586]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_585, A_586))=k3_xboole_0(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_53096])).
% 29.53/17.29  tff(c_47053, plain, (![A_452, C_453, B_8]: (k2_zfmisc_1(k3_xboole_0(A_452, k1_xboole_0), k3_xboole_0(C_453, B_8))=k3_xboole_0(k2_zfmisc_1(A_452, C_453), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_46978])).
% 29.53/17.29  tff(c_48067, plain, (![A_480, C_481, B_482]: (k2_zfmisc_1(k3_xboole_0(A_480, k1_xboole_0), k3_xboole_0(C_481, B_482))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_480, C_481)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_47053])).
% 29.53/17.29  tff(c_48161, plain, (![A_480]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_480, k2_zfmisc_1('#skF_1', '#skF_2')))=k2_zfmisc_1(k3_xboole_0(A_480, k1_xboole_0), k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_45953, c_48067])).
% 29.53/17.29  tff(c_53543, plain, (![A_590]: (k2_zfmisc_1(k3_xboole_0(A_590, k1_xboole_0), k2_zfmisc_1('#skF_1', '#skF_2'))=k3_xboole_0(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_53275, c_48161])).
% 29.53/17.29  tff(c_53621, plain, (![A_590]: (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_xboole_0(A_590, k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_53543, c_8])).
% 29.53/17.29  tff(c_53661, plain, (![A_590]: (k3_xboole_0(A_590, k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_22, c_53621])).
% 29.53/17.29  tff(c_54589, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_53661])).
% 29.53/17.29  tff(c_47744, plain, (![A_471, B_472, D_473]: (k2_zfmisc_1(k3_xboole_0(A_471, B_472), k3_xboole_0(k1_xboole_0, D_473))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_472, D_473)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_46978])).
% 29.53/17.29  tff(c_47843, plain, (![D_473]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1('#skF_3', D_473))=k2_zfmisc_1('#skF_1', k3_xboole_0(k1_xboole_0, D_473)))), inference(superposition, [status(thm), theory('equality')], [c_45954, c_47744])).
% 29.53/17.29  tff(c_53312, plain, (![D_473]: (k2_zfmisc_1('#skF_1', k3_xboole_0(k1_xboole_0, D_473))=k3_xboole_0(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_53275, c_47843])).
% 29.53/17.29  tff(c_53618, plain, (![A_590, C_15, D_16]: (k3_xboole_0(A_590, k1_xboole_0)=C_15 | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_xboole_0(A_590, k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_zfmisc_1(C_15, D_16))), inference(superposition, [status(thm), theory('equality')], [c_53543, c_18])).
% 29.53/17.29  tff(c_54932, plain, (![A_606, C_607, D_608]: (k3_xboole_0(A_606, k1_xboole_0)=C_607 | k3_xboole_0(A_606, k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_zfmisc_1(C_607, D_608))), inference(negUnitSimplification, [status(thm)], [c_22, c_53618])).
% 29.53/17.29  tff(c_54969, plain, (![A_609]: (k3_xboole_0(A_609, k1_xboole_0)='#skF_1' | k3_xboole_0(A_609, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_53312, c_54932])).
% 29.53/17.29  tff(c_48397, plain, (![A_488, A_489, C_490]: (k2_zfmisc_1(k3_xboole_0(A_488, A_489), k3_xboole_0(C_490, k1_xboole_0))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_488, C_490)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_47059])).
% 29.53/17.29  tff(c_48522, plain, (![A_1, B_2, C_490]: (k2_zfmisc_1(k3_xboole_0(A_1, B_2), k3_xboole_0(C_490, k1_xboole_0))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_2, C_490)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_48397])).
% 29.53/17.29  tff(c_54761, plain, (![A_1, B_2, C_490]: (k2_zfmisc_1(k3_xboole_0(A_1, B_2), k3_xboole_0(C_490, k1_xboole_0))=k3_xboole_0(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_53275, c_48522])).
% 29.53/17.29  tff(c_54977, plain, (![C_490, A_609]: (k2_zfmisc_1(k1_xboole_0, k3_xboole_0(C_490, k1_xboole_0))=k3_xboole_0(k1_xboole_0, k1_xboole_0) | k3_xboole_0(A_609, k1_xboole_0)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_54969, c_54761])).
% 29.53/17.29  tff(c_55192, plain, (![A_609]: (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k3_xboole_0(A_609, k1_xboole_0)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_54977])).
% 29.53/17.29  tff(c_55274, plain, (![A_610]: (k3_xboole_0(A_610, k1_xboole_0)='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54589, c_55192])).
% 29.53/17.29  tff(c_55418, plain, (![A_610]: (r1_tarski('#skF_1', A_610))), inference(superposition, [status(thm), theory('equality')], [c_55274, c_4])).
% 29.53/17.29  tff(c_55406, plain, (![B_4]: (k3_xboole_0(k1_xboole_0, B_4)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_55274, c_45955])).
% 29.53/17.29  tff(c_47846, plain, (![B_2, A_1, D_473]: (k2_zfmisc_1(k3_xboole_0(B_2, A_1), k3_xboole_0(k1_xboole_0, D_473))=k3_xboole_0(k1_xboole_0, k2_zfmisc_1(B_2, D_473)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_47744])).
% 29.53/17.29  tff(c_56273, plain, (![B_621, A_622]: (k2_zfmisc_1(k3_xboole_0(B_621, A_622), '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55406, c_55406, c_47846])).
% 29.53/17.29  tff(c_55193, plain, (![A_609]: (k3_xboole_0(A_609, k1_xboole_0)='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54589, c_55192])).
% 29.53/17.29  tff(c_55263, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_55193, c_54589])).
% 29.53/17.29  tff(c_53660, plain, (![A_590, C_15, D_16]: (k3_xboole_0(A_590, k1_xboole_0)=C_15 | k3_xboole_0(A_590, k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k2_zfmisc_1(C_15, D_16))), inference(negUnitSimplification, [status(thm)], [c_22, c_53618])).
% 29.53/17.29  tff(c_55260, plain, (![C_15, D_16]: (C_15='#skF_1' | k1_xboole_0='#skF_1' | k2_zfmisc_1(C_15, D_16)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55193, c_55193, c_55193, c_53660])).
% 29.53/17.29  tff(c_56013, plain, (![C_15, D_16]: (C_15='#skF_1' | k2_zfmisc_1(C_15, D_16)!='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_55263, c_55260])).
% 29.53/17.29  tff(c_56359, plain, (![B_621, A_622]: (k3_xboole_0(B_621, A_622)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56273, c_56013])).
% 29.53/17.29  tff(c_56940, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56359, c_45953])).
% 29.53/17.29  tff(c_56347, plain, (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_45953, c_56273])).
% 29.53/17.29  tff(c_56431, plain, (![D_16, C_15]: (D_16='#skF_1' | k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k2_zfmisc_1(C_15, D_16)!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56347, c_16])).
% 29.53/17.29  tff(c_56446, plain, (![D_16, C_15]: (D_16='#skF_1' | k2_zfmisc_1(C_15, D_16)!='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_22, c_55263, c_56431])).
% 29.53/17.29  tff(c_57020, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_56940, c_56446])).
% 29.53/17.29  tff(c_57029, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57020, c_45927])).
% 29.53/17.29  tff(c_57033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55418, c_57029])).
% 29.53/17.29  tff(c_57050, plain, (![A_629]: (k3_xboole_0(A_629, k1_xboole_0)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_53661])).
% 29.53/17.29  tff(c_57194, plain, (![A_629]: (r1_tarski(k1_xboole_0, A_629))), inference(superposition, [status(thm), theory('equality')], [c_57050, c_4])).
% 29.53/17.29  tff(c_94919, plain, (![A_629]: (r1_tarski('#skF_2', A_629))), inference(demodulation, [status(thm), theory('equality')], [c_94894, c_57194])).
% 29.53/17.29  tff(c_94933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94919, c_45927])).
% 29.53/17.29  tff(c_94934, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_94840])).
% 29.53/17.29  tff(c_95550, plain, (r1_tarski('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_94934, c_4])).
% 29.53/17.29  tff(c_95675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45927, c_95550])).
% 29.53/17.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.53/17.29  
% 29.53/17.29  Inference rules
% 29.53/17.29  ----------------------
% 29.53/17.29  #Ref     : 23
% 29.53/17.29  #Sup     : 25379
% 29.53/17.29  #Fact    : 1
% 29.53/17.29  #Define  : 0
% 29.53/17.29  #Split   : 12
% 29.53/17.29  #Chain   : 0
% 29.53/17.29  #Close   : 0
% 29.53/17.29  
% 29.53/17.29  Ordering : KBO
% 29.53/17.29  
% 29.53/17.29  Simplification rules
% 29.53/17.29  ----------------------
% 29.53/17.29  #Subsume      : 1410
% 29.53/17.29  #Demod        : 36440
% 29.53/17.29  #Tautology    : 12828
% 29.53/17.29  #SimpNegUnit  : 424
% 29.53/17.29  #BackRed      : 543
% 29.53/17.29  
% 29.53/17.29  #Partial instantiations: 0
% 29.53/17.29  #Strategies tried      : 1
% 29.53/17.29  
% 29.53/17.29  Timing (in seconds)
% 29.53/17.29  ----------------------
% 29.53/17.30  Preprocessing        : 0.31
% 29.53/17.30  Parsing              : 0.16
% 29.53/17.30  CNF conversion       : 0.02
% 29.53/17.30  Main loop            : 16.14
% 29.53/17.30  Inferencing          : 1.52
% 29.53/17.30  Reduction            : 10.80
% 29.53/17.30  Demodulation         : 10.02
% 29.53/17.30  BG Simplification    : 0.25
% 29.53/17.30  Subsumption          : 2.65
% 29.53/17.30  Abstraction          : 0.37
% 29.53/17.30  MUC search           : 0.00
% 29.53/17.30  Cooper               : 0.00
% 29.53/17.30  Total                : 16.51
% 29.53/17.30  Index Insertion      : 0.00
% 29.53/17.30  Index Deletion       : 0.00
% 29.53/17.30  Index Matching       : 0.00
% 29.53/17.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
