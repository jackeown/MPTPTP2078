%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0325+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:06 EST 2020

% Result     : Theorem 25.42s
% Output     : CNFRefutation 25.56s
% Verified   : 
% Statistics : Number of formulae       :  169 (3180 expanded)
%              Number of leaves         :   18 (1043 expanded)
%              Depth                    :   19
%              Number of atoms          :  228 (6067 expanded)
%              Number of equality atoms :  185 (4737 expanded)
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

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_8,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_98,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_98])).

tff(c_694,plain,(
    ! [A_51,C_52,B_53,D_54] : k3_xboole_0(k2_zfmisc_1(A_51,C_52),k2_zfmisc_1(B_53,D_54)) = k2_zfmisc_1(k3_xboole_0(A_51,B_53),k3_xboole_0(C_52,D_54)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2201,plain,(
    ! [A_89,B_90,D_91] : k2_zfmisc_1(k3_xboole_0(A_89,B_90),k3_xboole_0(k1_xboole_0,D_91)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_90,D_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_694])).

tff(c_33088,plain,(
    ! [D_365] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'),D_365)) = k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k3_xboole_0(k1_xboole_0,D_365)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_2201])).

tff(c_33214,plain,(
    k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33088])).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_715,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_108])).

tff(c_775,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_715])).

tff(c_14,plain,(
    ! [C_11,A_9,B_10,D_12] :
      ( C_11 = A_9
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(C_11,D_12) != k2_zfmisc_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_939,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0('#skF_1','#skF_3') = A_9
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(A_9,B_10) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_14])).

tff(c_31160,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_939])).

tff(c_31198,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_31160])).

tff(c_22,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1885,plain,(
    ! [B_83,B_84,D_85] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_83),k3_xboole_0(B_84,D_85)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_83,D_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_694])).

tff(c_2348,plain,(
    ! [B_92] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_92,k2_zfmisc_1('#skF_3','#skF_4'))) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_92),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1885])).

tff(c_2434,plain,(
    k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k1_xboole_0),k2_zfmisc_1('#skF_1','#skF_2')) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2348])).

tff(c_2673,plain,(
    ! [C_11,D_12] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = C_11
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2434,c_14])).

tff(c_2683,plain,(
    ! [C_11,D_12] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = C_11
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_2673])).

tff(c_2960,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2683])).

tff(c_766,plain,(
    ! [B_53,B_4,D_54] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_53),k3_xboole_0(B_4,D_54)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_53,D_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_694])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k3_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1076,plain,(
    ! [A_59,B_60,C_61,D_62] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_59,B_60),k3_xboole_0(C_61,D_62)),k2_zfmisc_1(A_59,C_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_16])).

tff(c_4149,plain,(
    ! [A_105,B_106,C_107,D_108] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_105,B_106),k3_xboole_0(C_107,D_108)),k2_zfmisc_1(B_106,C_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1076])).

tff(c_4355,plain,(
    ! [B_109,D_110,B_111] : r1_tarski(k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_109,D_110)),k2_zfmisc_1(B_109,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_4149])).

tff(c_4409,plain,(
    ! [A_3,B_111] : r1_tarski(k3_xboole_0(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(A_3,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4355])).

tff(c_4428,plain,(
    ! [A_112,B_113] : r1_tarski(k1_xboole_0,k2_zfmisc_1(A_112,B_113)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2960,c_4409])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4448,plain,(
    ! [A_112,B_113] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_112,B_113)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4428,c_18])).

tff(c_4993,plain,(
    ! [B_124,B_125,D_126] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_124),k3_xboole_0(B_125,D_126)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4448,c_766])).

tff(c_5154,plain,(
    ! [B_127] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_127),k2_zfmisc_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_4993])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5213,plain,(
    ! [B_127] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,B_127) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5154,c_4])).

tff(c_5273,plain,(
    ! [B_128] : k3_xboole_0(k1_xboole_0,B_128) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_5213])).

tff(c_49,plain,(
    ! [B_21,A_22] : k3_xboole_0(B_21,A_22) = k3_xboole_0(A_22,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,(
    ! [B_21,A_22] : r1_tarski(k3_xboole_0(B_21,A_22),A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_16])).

tff(c_5381,plain,(
    ! [B_128] : r1_tarski(k1_xboole_0,B_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_5273,c_64])).

tff(c_31253,plain,(
    ! [B_128] : r1_tarski('#skF_1',B_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31198,c_5381])).

tff(c_31267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31253,c_48])).

tff(c_31268,plain,
    ( k1_xboole_0 = '#skF_2'
    | k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_31160])).

tff(c_31270,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_31268])).

tff(c_31730,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_31270,c_64])).

tff(c_31803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_31730])).

tff(c_31804,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_31268])).

tff(c_31819,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31804,c_31804,c_6])).

tff(c_31821,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31804,c_22])).

tff(c_32128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31819,c_31821])).

tff(c_32129,plain,(
    ! [C_11,D_12] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = C_11
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(splitRight,[status(thm)],[c_2683])).

tff(c_33294,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_33214,c_32129])).

tff(c_32130,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2683])).

tff(c_12,plain,(
    ! [D_12,B_10,A_9,C_11] :
      ( D_12 = B_10
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(C_11,D_12) != k2_zfmisc_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_33283,plain,(
    ! [D_12,C_11] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = D_12
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33214,c_12])).

tff(c_33299,plain,(
    ! [D_12,C_11] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = D_12
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_32130,c_33283])).

tff(c_33953,plain,(
    ! [D_12,C_11] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = D_12
      | k2_zfmisc_1(C_11,D_12) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33294,c_33294,c_33299])).

tff(c_33956,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_33953])).

tff(c_33989,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33956,c_33294])).

tff(c_33289,plain,(
    ! [C_11,D_12] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_11
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33214,c_14])).

tff(c_33300,plain,(
    ! [C_11,D_12] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_11
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_32130,c_33289])).

tff(c_35221,plain,(
    ! [C_380,D_381] :
      ( C_380 = '#skF_2'
      | k2_zfmisc_1(C_380,D_381) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33989,c_33956,c_33300])).

tff(c_35243,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_33956,c_35221])).

tff(c_35252,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35243,c_33989])).

tff(c_769,plain,(
    ! [A_51,C_52,B_4] : k2_zfmisc_1(k3_xboole_0(A_51,k1_xboole_0),k3_xboole_0(C_52,B_4)) = k3_xboole_0(k2_zfmisc_1(A_51,C_52),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_694])).

tff(c_784,plain,(
    ! [A_51,C_52,B_4] : k2_zfmisc_1(k3_xboole_0(A_51,k1_xboole_0),k3_xboole_0(C_52,B_4)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_51,C_52)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_769])).

tff(c_36327,plain,(
    ! [A_382,B_383,B_384] : k2_zfmisc_1(k3_xboole_0(A_382,B_383),k3_xboole_0(B_384,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_383,B_384)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2201])).

tff(c_36456,plain,(
    ! [C_52,A_51] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,C_52)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_51,C_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_36327])).

tff(c_36531,plain,(
    ! [A_51,C_52] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_51,C_52)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35252,c_8,c_36456])).

tff(c_110,plain,(
    ! [A_13,B_14] : k3_xboole_0(k3_xboole_0(A_13,B_14),A_13) = k3_xboole_0(A_13,B_14) ),
    inference(resolution,[status(thm)],[c_16,c_98])).

tff(c_1986,plain,(
    ! [B_83,A_13,B_14] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_83),k3_xboole_0(A_13,B_14)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_83,A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_1885])).

tff(c_36814,plain,(
    ! [B_391,A_392,B_393] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_391),k3_xboole_0(A_392,B_393)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36531,c_1986])).

tff(c_33985,plain,(
    ! [D_12,C_11] :
      ( D_12 = '#skF_2'
      | k2_zfmisc_1(C_11,D_12) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33956,c_33956,c_33953])).

tff(c_36644,plain,(
    ! [D_12,C_11] :
      ( D_12 = '#skF_1'
      | k2_zfmisc_1(C_11,D_12) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35243,c_35243,c_33985])).

tff(c_36955,plain,(
    ! [A_392,B_393] : k3_xboole_0(A_392,B_393) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_36814,c_36644])).

tff(c_37008,plain,(
    ! [A_22] : r1_tarski('#skF_1',A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36955,c_64])).

tff(c_37035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37008,c_48])).

tff(c_37037,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_37087,plain,(
    ! [A_400,B_401] :
      ( k3_xboole_0(A_400,B_401) = A_400
      | ~ r1_tarski(A_400,B_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37101,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_37037,c_37087])).

tff(c_38124,plain,(
    ! [A_430,C_431,B_432,D_433] : k3_xboole_0(k2_zfmisc_1(A_430,C_431),k2_zfmisc_1(B_432,D_433)) = k2_zfmisc_1(k3_xboole_0(A_430,B_432),k3_xboole_0(C_431,D_433)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38205,plain,(
    ! [A_430,C_431,B_4] : k2_zfmisc_1(k3_xboole_0(A_430,k1_xboole_0),k3_xboole_0(C_431,B_4)) = k3_xboole_0(k2_zfmisc_1(A_430,C_431),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_38124])).

tff(c_38911,plain,(
    ! [A_450,C_451,B_452] : k2_zfmisc_1(k3_xboole_0(A_450,k1_xboole_0),k3_xboole_0(C_451,B_452)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_450,C_451)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38205])).

tff(c_40564,plain,(
    ! [A_488] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_488,'#skF_1')) = k2_zfmisc_1(k3_xboole_0(A_488,k1_xboole_0),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37101,c_38911])).

tff(c_40678,plain,(
    k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k1_xboole_0),'#skF_1') = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_40564])).

tff(c_37036,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_37102,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_37087])).

tff(c_38199,plain,(
    ! [A_430,A_3,C_431] : k2_zfmisc_1(k3_xboole_0(A_430,A_3),k3_xboole_0(C_431,k1_xboole_0)) = k3_xboole_0(k2_zfmisc_1(A_430,C_431),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_38124])).

tff(c_38620,plain,(
    ! [A_442,A_443,C_444] : k2_zfmisc_1(k3_xboole_0(A_442,A_443),k3_xboole_0(C_444,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_442,C_444)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_38199])).

tff(c_41478,plain,(
    ! [C_499] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_499)) = k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k3_xboole_0(C_499,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37102,c_38620])).

tff(c_41624,plain,(
    k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_41478])).

tff(c_42289,plain,(
    ! [C_11,D_12] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_11
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41624,c_14])).

tff(c_42299,plain,(
    ! [C_11,D_12] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_11
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_42289])).

tff(c_42376,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42299])).

tff(c_38196,plain,(
    ! [A_3,B_432,D_433] : k2_zfmisc_1(k3_xboole_0(A_3,B_432),k3_xboole_0(k1_xboole_0,D_433)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_432,D_433)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_38124])).

tff(c_38286,plain,(
    ! [A_434,B_435,C_436,D_437] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_434,B_435),k3_xboole_0(C_436,D_437)),k2_zfmisc_1(A_434,C_436)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38124,c_16])).

tff(c_42927,plain,(
    ! [A_512,B_513,B_514,A_515] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_512,B_513),k3_xboole_0(B_514,A_515)),k2_zfmisc_1(A_512,A_515)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_38286])).

tff(c_43358,plain,(
    ! [B_520,D_521,A_522] : r1_tarski(k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_520,D_521)),k2_zfmisc_1(A_522,D_521)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38196,c_42927])).

tff(c_43433,plain,(
    ! [A_522,B_4] : r1_tarski(k3_xboole_0(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(A_522,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_43358])).

tff(c_43450,plain,(
    ! [A_523,B_524] : r1_tarski(k1_xboole_0,k2_zfmisc_1(A_523,B_524)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42376,c_43433])).

tff(c_43472,plain,(
    ! [A_523,B_524] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_523,B_524)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_43450,c_18])).

tff(c_39010,plain,(
    ! [A_450] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_450,'#skF_1')) = k2_zfmisc_1(k3_xboole_0(A_450,k1_xboole_0),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37101,c_38911])).

tff(c_44233,plain,(
    ! [A_532] : k2_zfmisc_1(k3_xboole_0(A_532,k1_xboole_0),'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_43472,c_39010])).

tff(c_44343,plain,(
    ! [A_532] :
      ( k1_xboole_0 = '#skF_1'
      | k3_xboole_0(A_532,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44233,c_4])).

tff(c_44515,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_44343])).

tff(c_44533,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44515,c_44515,c_8])).

tff(c_44534,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44515,c_22])).

tff(c_44648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44533,c_44534])).

tff(c_44650,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_44343])).

tff(c_38166,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38124,c_37102])).

tff(c_38219,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37101,c_2,c_38166])).

tff(c_38234,plain,(
    ! [B_10,A_9] :
      ( k3_xboole_0('#skF_4','#skF_2') = B_10
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(A_9,B_10) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38219,c_12])).

tff(c_80693,plain,
    ( k3_xboole_0('#skF_4','#skF_2') = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_38234])).

tff(c_80694,plain,
    ( k3_xboole_0('#skF_4','#skF_2') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44650,c_80693])).

tff(c_80748,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_80694])).

tff(c_44660,plain,(
    ! [A_537] : k3_xboole_0(A_537,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44343])).

tff(c_44809,plain,(
    ! [A_537] : r1_tarski(k1_xboole_0,A_537) ),
    inference(superposition,[status(thm),theory(equality)],[c_44660,c_16])).

tff(c_80772,plain,(
    ! [A_537] : r1_tarski('#skF_2',A_537) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80748,c_44809])).

tff(c_80787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80772,c_37036])).

tff(c_80788,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_80694])).

tff(c_81419,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_80788,c_16])).

tff(c_81544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37036,c_81419])).

tff(c_81546,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42299])).

tff(c_42283,plain,(
    ! [D_12,C_11] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = D_12
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41624,c_12])).

tff(c_42298,plain,(
    ! [D_12,C_11] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = D_12
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_42283])).

tff(c_81950,plain,(
    ! [D_876,C_877] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = D_876
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_877,D_876) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81546,c_42298])).

tff(c_81989,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_40678,c_81950])).

tff(c_37103,plain,(
    ! [A_13,B_14] : k3_xboole_0(k3_xboole_0(A_13,B_14),A_13) = k3_xboole_0(A_13,B_14) ),
    inference(resolution,[status(thm)],[c_16,c_37087])).

tff(c_39518,plain,(
    ! [B_466,B_467,D_468] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_466),k3_xboole_0(B_467,D_468)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_466,D_468)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_38124])).

tff(c_83515,plain,(
    ! [B_893,A_894,B_895] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,B_893),k3_xboole_0(A_894,B_895)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_893,A_894)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37103,c_39518])).

tff(c_83658,plain,(
    ! [B_432,D_433] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_432,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_432,D_433)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38196,c_83515])).

tff(c_83752,plain,(
    ! [B_432,D_433] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_432,D_433)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81989,c_6,c_83658])).

tff(c_38711,plain,(
    ! [C_444] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1('#skF_1',C_444)) = k2_zfmisc_1('#skF_1',k3_xboole_0(C_444,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37101,c_38620])).

tff(c_84029,plain,(
    ! [C_900] : k2_zfmisc_1('#skF_1',k3_xboole_0(C_900,k1_xboole_0)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83752,c_38711])).

tff(c_81949,plain,(
    ! [D_12,C_11] :
      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = D_12
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81546,c_42298])).

tff(c_81991,plain,(
    ! [D_12,C_11] :
      ( D_12 = '#skF_1'
      | k2_zfmisc_1(C_11,D_12) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81989,c_81989,c_81949])).

tff(c_84174,plain,(
    ! [C_901] : k3_xboole_0(C_901,k1_xboole_0) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_84029,c_81991])).

tff(c_84312,plain,(
    ! [C_901] : r1_tarski('#skF_1',C_901) ),
    inference(superposition,[status(thm),theory(equality)],[c_84174,c_16])).

tff(c_39211,plain,(
    ! [A_458,B_459,D_460] : k2_zfmisc_1(k3_xboole_0(A_458,B_459),k3_xboole_0(k1_xboole_0,D_460)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(B_459,D_460)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_38124])).

tff(c_40887,plain,(
    ! [D_492] : k3_xboole_0(k1_xboole_0,k2_zfmisc_1('#skF_3',D_492)) = k2_zfmisc_1('#skF_1',k3_xboole_0(k1_xboole_0,D_492)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37101,c_39211])).

tff(c_41019,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_40887])).

tff(c_81995,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81989,c_81989,c_41019])).

tff(c_81545,plain,(
    ! [C_11,D_12] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_11
      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(C_11,D_12) ) ),
    inference(splitRight,[status(thm)],[c_42299])).

tff(c_82441,plain,(
    ! [C_878,D_879] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_878
      | k2_zfmisc_1(C_878,D_879) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81989,c_81545])).

tff(c_82460,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_81995,c_82441])).

tff(c_83476,plain,(
    ! [D_891,C_892] :
      ( D_891 = '#skF_1'
      | k2_zfmisc_1(C_892,D_891) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81989,c_81989,c_81949])).

tff(c_83504,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_82460,c_83476])).

tff(c_83509,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83504,c_37036])).

tff(c_84380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84312,c_83509])).

%------------------------------------------------------------------------------
