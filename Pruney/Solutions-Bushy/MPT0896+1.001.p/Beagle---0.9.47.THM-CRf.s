%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0896+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:02 EST 2020

% Result     : Theorem 5.03s
% Output     : CNFRefutation 5.58s
% Verified   : 
% Statistics : Number of formulae       :  303 (5797 expanded)
%              Number of leaves         :   20 (1694 expanded)
%              Depth                    :   20
%              Number of atoms          :  621 (20108 expanded)
%              Number of equality atoms :  599 (20086 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

tff(f_26,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_78,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_zfmisc_1(k3_zfmisc_1(A_1,B_2,C_3),D_4) = k4_zfmisc_1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_189,plain,(
    ! [D_44,B_45,A_46,C_47] :
      ( D_44 = B_45
      | k1_xboole_0 = B_45
      | k1_xboole_0 = A_46
      | k2_zfmisc_1(C_47,D_44) != k2_zfmisc_1(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_196,plain,(
    ! [B_49,A_53,D_48,C_51,B_50,A_52] :
      ( D_48 = B_49
      | k1_xboole_0 = B_49
      | k1_xboole_0 = A_53
      | k4_zfmisc_1(A_52,B_50,C_51,D_48) != k2_zfmisc_1(A_53,B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_189])).

tff(c_212,plain,(
    ! [B_54,A_55] :
      ( B_54 = '#skF_8'
      | k1_xboole_0 = B_54
      | k1_xboole_0 = A_55
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(A_55,B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_196])).

tff(c_215,plain,(
    ! [D_4,A_1,B_2,C_3] :
      ( D_4 = '#skF_8'
      | k1_xboole_0 = D_4
      | k3_zfmisc_1(A_1,B_2,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_212])).

tff(c_218,plain,
    ( '#skF_8' = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_215])).

tff(c_219,plain,
    ( '#skF_8' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_218])).

tff(c_238,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] :
      ( k3_zfmisc_1(A_9,B_10,C_11) != k1_xboole_0
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_242,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_8])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_242])).

tff(c_252,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_256,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_32])).

tff(c_369,plain,(
    ! [D_88,B_89,D_86,C_90,A_91,C_87] :
      ( D_88 = D_86
      | k1_xboole_0 = D_88
      | k3_zfmisc_1(A_91,B_89,C_90) = k1_xboole_0
      | k4_zfmisc_1(A_91,B_89,C_90,D_88) != k2_zfmisc_1(C_87,D_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_189])).

tff(c_372,plain,(
    ! [D_86,C_87] :
      ( D_86 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_87,D_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_369])).

tff(c_385,plain,(
    ! [D_86,C_87] :
      ( D_86 = '#skF_4'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_87,D_86) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_372])).

tff(c_389,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_418,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_8])).

tff(c_420,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_253,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_427,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_253])).

tff(c_439,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_24])).

tff(c_14,plain,(
    ! [B_10,C_11] : k3_zfmisc_1(k1_xboole_0,B_10,C_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_83,plain,(
    ! [A_24,B_25,C_26,D_27] : k2_zfmisc_1(k3_zfmisc_1(A_24,B_25,C_26),D_27) = k4_zfmisc_1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_98,plain,(
    ! [B_10,C_11,D_27] : k4_zfmisc_1(k1_xboole_0,B_10,C_11,D_27) = k2_zfmisc_1(k1_xboole_0,D_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_83])).

tff(c_432,plain,(
    ! [B_10,C_11,D_27] : k4_zfmisc_1('#skF_5',B_10,C_11,D_27) = k2_zfmisc_1('#skF_5',D_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_420,c_98])).

tff(c_546,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_zfmisc_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_256])).

tff(c_178,plain,(
    ! [C_40,A_41,B_42,D_43] :
      ( C_40 = A_41
      | k1_xboole_0 = B_42
      | k1_xboole_0 = A_41
      | k2_zfmisc_1(C_40,D_43) != k2_zfmisc_1(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_184,plain,(
    ! [B_2,C_3,A_1,D_4,D_43,C_40] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = C_40
      | k1_xboole_0 = D_4
      | k3_zfmisc_1(A_1,B_2,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k2_zfmisc_1(C_40,D_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_446,plain,(
    ! [B_2,C_3,A_1,D_4,D_43,C_40] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = C_40
      | D_4 = '#skF_5'
      | k3_zfmisc_1(A_1,B_2,C_3) = '#skF_5'
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k2_zfmisc_1(C_40,D_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_420,c_184])).

tff(c_586,plain,(
    ! [C_40,D_43] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_40
      | '#skF_5' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_5'
      | k2_zfmisc_1(C_40,D_43) != k2_zfmisc_1('#skF_5','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_446])).

tff(c_590,plain,(
    ! [C_40,D_43] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_40
      | k2_zfmisc_1(C_40,D_43) != k2_zfmisc_1('#skF_5','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_439,c_586])).

tff(c_659,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_5' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_590])).

tff(c_661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_659])).

tff(c_662,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_664,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_662])).

tff(c_672,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_253])).

tff(c_684,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_24])).

tff(c_10,plain,(
    ! [A_9,B_10] : k3_zfmisc_1(A_9,B_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,(
    ! [A_9,B_10,D_27] : k4_zfmisc_1(A_9,B_10,k1_xboole_0,D_27) = k2_zfmisc_1(k1_xboole_0,D_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_83])).

tff(c_679,plain,(
    ! [A_9,B_10,D_27] : k4_zfmisc_1(A_9,B_10,'#skF_7',D_27) = k2_zfmisc_1('#skF_7',D_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_664,c_92])).

tff(c_771,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_zfmisc_1('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_256])).

tff(c_691,plain,(
    ! [B_2,C_3,A_1,D_4,D_43,C_40] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = C_40
      | D_4 = '#skF_7'
      | k3_zfmisc_1(A_1,B_2,C_3) = '#skF_7'
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k2_zfmisc_1(C_40,D_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_664,c_184])).

tff(c_831,plain,(
    ! [C_40,D_43] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_40
      | '#skF_7' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_40,D_43) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_691])).

tff(c_835,plain,(
    ! [C_40,D_43] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_40
      | k2_zfmisc_1(C_40,D_43) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_672,c_684,c_831])).

tff(c_904,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_835])).

tff(c_906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_672,c_904])).

tff(c_907,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_917,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_253])).

tff(c_929,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_24])).

tff(c_415,plain,(
    ! [D_4] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_4) = k2_zfmisc_1(k1_xboole_0,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_2])).

tff(c_1043,plain,(
    ! [D_4] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_4) = k2_zfmisc_1('#skF_6',D_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_415])).

tff(c_1044,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_zfmisc_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1043,c_256])).

tff(c_936,plain,(
    ! [B_2,C_3,A_1,D_4,D_43,C_40] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = C_40
      | D_4 = '#skF_6'
      | k3_zfmisc_1(A_1,B_2,C_3) = '#skF_6'
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k2_zfmisc_1(C_40,D_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_907,c_184])).

tff(c_1074,plain,(
    ! [C_40,D_43] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_40
      | '#skF_6' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k2_zfmisc_1(C_40,D_43) != k2_zfmisc_1('#skF_6','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_936])).

tff(c_1078,plain,(
    ! [C_40,D_43] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_40
      | k2_zfmisc_1(C_40,D_43) != k2_zfmisc_1('#skF_6','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_917,c_929,c_1074])).

tff(c_1178,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1078])).

tff(c_1180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_917,c_1178])).

tff(c_1182,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_1238,plain,(
    ! [B_212,C_211,D_209,A_214,D_210,C_213] :
      ( k3_zfmisc_1(A_214,B_212,C_213) = C_211
      | k1_xboole_0 = D_210
      | k3_zfmisc_1(A_214,B_212,C_213) = k1_xboole_0
      | k4_zfmisc_1(A_214,B_212,C_213,D_210) != k2_zfmisc_1(C_211,D_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_1241,plain,(
    ! [C_211,D_209] :
      ( k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = C_211
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_211,D_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_1238])).

tff(c_1258,plain,(
    ! [C_215,D_216] :
      ( k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = C_215
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_215,D_216) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1182,c_24,c_1241])).

tff(c_1261,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = k3_zfmisc_1('#skF_5','#skF_6','#skF_7')
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1258])).

tff(c_1264,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1261])).

tff(c_20,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13] :
      ( D_15 = A_12
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k3_zfmisc_1(D_15,E_16,F_17) != k3_zfmisc_1(A_12,B_13,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1298,plain,(
    ! [A_12,C_14,B_13] :
      ( A_12 = '#skF_5'
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k3_zfmisc_1(A_12,B_13,C_14) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_20])).

tff(c_1450,plain,
    ( '#skF_5' = '#skF_1'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1298])).

tff(c_1452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_78,c_1450])).

tff(c_1453,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1459,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1453])).

tff(c_1454,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1460,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1454,c_32])).

tff(c_1531,plain,(
    ! [D_261,B_262,A_263,C_264] :
      ( D_261 = B_262
      | k1_xboole_0 = B_262
      | k1_xboole_0 = A_263
      | k2_zfmisc_1(C_264,D_261) != k2_zfmisc_1(A_263,B_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1676,plain,(
    ! [D_303,C_301,D_299,B_300,A_302,C_298] :
      ( D_303 = D_299
      | k1_xboole_0 = D_299
      | k3_zfmisc_1(A_302,B_300,C_301) = k1_xboole_0
      | k4_zfmisc_1(A_302,B_300,C_301,D_299) != k2_zfmisc_1(C_298,D_303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1531])).

tff(c_1691,plain,(
    ! [D_303,C_298] :
      ( D_303 = '#skF_8'
      | k1_xboole_0 = '#skF_8'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_298,D_303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1460,c_1676])).

tff(c_1714,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1691])).

tff(c_1739,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1714,c_8])).

tff(c_1747,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1739])).

tff(c_1749,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1747])).

tff(c_1481,plain,(
    ! [A_251,B_252,C_253,D_254] : k2_zfmisc_1(k3_zfmisc_1(A_251,B_252,C_253),D_254) = k4_zfmisc_1(A_251,B_252,C_253,D_254) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1496,plain,(
    ! [B_10,C_11,D_254] : k4_zfmisc_1(k1_xboole_0,B_10,C_11,D_254) = k2_zfmisc_1(k1_xboole_0,D_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1481])).

tff(c_1761,plain,(
    ! [B_10,C_11,D_254] : k4_zfmisc_1('#skF_6',B_10,C_11,D_254) = k2_zfmisc_1('#skF_6',D_254) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_1749,c_1496])).

tff(c_1770,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_30])).

tff(c_1767,plain,(
    '#skF_6' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_28])).

tff(c_1769,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_26])).

tff(c_1768,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_24])).

tff(c_1736,plain,(
    ! [D_4] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_4) = k2_zfmisc_1(k1_xboole_0,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_1714,c_2])).

tff(c_1839,plain,(
    ! [D_4] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_4) = k2_zfmisc_1('#skF_6',D_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_1736])).

tff(c_1840,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_zfmisc_1('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1839,c_1460])).

tff(c_1688,plain,(
    ! [C_301,B_2,C_3,A_1,D_4,D_299,B_300,A_302] :
      ( D_4 = D_299
      | k1_xboole_0 = D_299
      | k3_zfmisc_1(A_302,B_300,C_301) = k1_xboole_0
      | k4_zfmisc_1(A_302,B_300,C_301,D_299) != k4_zfmisc_1(A_1,B_2,C_3,D_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1676])).

tff(c_1964,plain,(
    ! [C_342,A_337,B_338,D_339,D_343,C_341,A_344,B_340] :
      ( D_343 = D_339
      | D_343 = '#skF_6'
      | k3_zfmisc_1(A_337,B_338,C_341) = '#skF_6'
      | k4_zfmisc_1(A_344,B_340,C_342,D_339) != k4_zfmisc_1(A_337,B_338,C_341,D_343) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_1749,c_1688])).

tff(c_1970,plain,(
    ! [D_339,A_344,B_340,C_342] :
      ( D_339 = '#skF_4'
      | '#skF_6' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k4_zfmisc_1(A_344,B_340,C_342,D_339) != k2_zfmisc_1('#skF_6','#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1840,c_1964])).

tff(c_1989,plain,(
    ! [D_339,A_344,B_340,C_342] :
      ( D_339 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k4_zfmisc_1(A_344,B_340,C_342,D_339) != k2_zfmisc_1('#skF_6','#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1768,c_1970])).

tff(c_2015,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1989])).

tff(c_1763,plain,(
    ! [A_9,B_10,C_11] :
      ( k3_zfmisc_1(A_9,B_10,C_11) != '#skF_6'
      | C_11 = '#skF_6'
      | B_10 = '#skF_6'
      | A_9 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_1749,c_1749,c_1749,c_8])).

tff(c_2019,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2015,c_1763])).

tff(c_2028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1770,c_1767,c_1769,c_2019])).

tff(c_2031,plain,(
    ! [D_353,A_354,B_355,C_356] :
      ( D_353 = '#skF_4'
      | k4_zfmisc_1(A_354,B_355,C_356,D_353) != k2_zfmisc_1('#skF_6','#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_1989])).

tff(c_2037,plain,(
    ! [D_254] :
      ( D_254 = '#skF_4'
      | k2_zfmisc_1('#skF_6',D_254) != k2_zfmisc_1('#skF_6','#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1761,c_2031])).

tff(c_2048,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2037])).

tff(c_2050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1459,c_2048])).

tff(c_2051,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1747])).

tff(c_2064,plain,(
    ! [B_10,C_11,D_254] : k4_zfmisc_1('#skF_7',B_10,C_11,D_254) = k2_zfmisc_1('#skF_7',D_254) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_2051,c_1496])).

tff(c_2073,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_30])).

tff(c_2070,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_28])).

tff(c_2072,plain,(
    '#skF_7' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_26])).

tff(c_2071,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_24])).

tff(c_2154,plain,(
    ! [D_4] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_4) = k2_zfmisc_1('#skF_7',D_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_1736])).

tff(c_2155,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_zfmisc_1('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_1460])).

tff(c_1578,plain,(
    ! [A_277,D_274,A_272,B_275,C_276,B_273] :
      ( D_274 = B_273
      | k1_xboole_0 = B_273
      | k1_xboole_0 = A_272
      | k4_zfmisc_1(A_277,B_275,C_276,D_274) != k2_zfmisc_1(A_272,B_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1531])).

tff(c_1590,plain,(
    ! [B_2,C_3,A_1,A_277,D_274,D_4,B_275,C_276] :
      ( D_4 = D_274
      | k1_xboole_0 = D_4
      | k3_zfmisc_1(A_1,B_2,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_277,B_275,C_276,D_274) != k4_zfmisc_1(A_1,B_2,C_3,D_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1578])).

tff(c_2258,plain,(
    ! [C_381,A_386,B_383,A_385,D_388,C_384,D_382,B_387] :
      ( D_388 = D_382
      | D_382 = '#skF_7'
      | k3_zfmisc_1(A_385,B_383,C_384) = '#skF_7'
      | k4_zfmisc_1(A_386,B_387,C_381,D_388) != k4_zfmisc_1(A_385,B_383,C_384,D_382) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_2051,c_1590])).

tff(c_2270,plain,(
    ! [D_388,A_386,B_387,C_381] :
      ( D_388 = '#skF_4'
      | '#skF_7' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k4_zfmisc_1(A_386,B_387,C_381,D_388) != k2_zfmisc_1('#skF_7','#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2155,c_2258])).

tff(c_2284,plain,(
    ! [D_388,A_386,B_387,C_381] :
      ( D_388 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k4_zfmisc_1(A_386,B_387,C_381,D_388) != k2_zfmisc_1('#skF_7','#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2071,c_2270])).

tff(c_2292,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2284])).

tff(c_2325,plain,(
    ! [A_390,B_391,C_392] :
      ( k3_zfmisc_1(A_390,B_391,C_392) != '#skF_7'
      | C_392 = '#skF_7'
      | B_391 = '#skF_7'
      | A_390 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_2051,c_2051,c_2051,c_8])).

tff(c_2328,plain,
    ( '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2292,c_2325])).

tff(c_2341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2073,c_2070,c_2072,c_2328])).

tff(c_2345,plain,(
    ! [D_393,A_394,B_395,C_396] :
      ( D_393 = '#skF_4'
      | k4_zfmisc_1(A_394,B_395,C_396,D_393) != k2_zfmisc_1('#skF_7','#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_2284])).

tff(c_2348,plain,(
    ! [D_254] :
      ( D_254 = '#skF_4'
      | k2_zfmisc_1('#skF_7',D_254) != k2_zfmisc_1('#skF_7','#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2064,c_2345])).

tff(c_2362,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2348])).

tff(c_2364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1459,c_2362])).

tff(c_2365,plain,(
    ! [D_303,C_298] :
      ( k1_xboole_0 = '#skF_8'
      | D_303 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_298,D_303) ) ),
    inference(splitRight,[status(thm)],[c_1691])).

tff(c_2371,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2365])).

tff(c_2393,plain,(
    '#skF_1' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_30])).

tff(c_2390,plain,(
    '#skF_2' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_28])).

tff(c_2392,plain,(
    '#skF_3' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_26])).

tff(c_1594,plain,(
    ! [B_278,A_279] :
      ( B_278 = '#skF_8'
      | k1_xboole_0 = B_278
      | k1_xboole_0 = A_279
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(A_279,B_278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1460,c_1578])).

tff(c_1597,plain,(
    ! [D_4,A_1,B_2,C_3] :
      ( D_4 = '#skF_8'
      | k1_xboole_0 = D_4
      | k3_zfmisc_1(A_1,B_2,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1594])).

tff(c_2713,plain,(
    ! [D_4,A_1,B_2,C_3] :
      ( D_4 = '#skF_8'
      | D_4 = '#skF_8'
      | k3_zfmisc_1(A_1,B_2,C_3) = '#skF_8'
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_2371,c_1597])).

tff(c_2716,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_8' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_8' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2713])).

tff(c_2717,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1459,c_1459,c_2716])).

tff(c_2386,plain,(
    ! [A_9,B_10,C_11] :
      ( k3_zfmisc_1(A_9,B_10,C_11) != '#skF_8'
      | C_11 = '#skF_8'
      | B_10 = '#skF_8'
      | A_9 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2371,c_2371,c_2371,c_2371,c_8])).

tff(c_2759,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2717,c_2386])).

tff(c_2771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2393,c_2390,c_2392,c_2759])).

tff(c_2774,plain,(
    ! [D_475,C_476] :
      ( D_475 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_476,D_475) ) ),
    inference(splitRight,[status(thm)],[c_2365])).

tff(c_2777,plain,(
    ! [D_4,A_1,B_2,C_3] :
      ( D_4 = '#skF_8'
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2774])).

tff(c_2780,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2777])).

tff(c_2782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1459,c_2780])).

tff(c_2783,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1453])).

tff(c_2789,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2783])).

tff(c_2784,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1453])).

tff(c_2790,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2784,c_1454,c_32])).

tff(c_2901,plain,(
    ! [D_497,B_498,A_499,C_500] :
      ( D_497 = B_498
      | k1_xboole_0 = B_498
      | k1_xboole_0 = A_499
      | k2_zfmisc_1(C_500,D_497) != k2_zfmisc_1(A_499,B_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3021,plain,(
    ! [C_535,D_532,B_533,A_536,C_534,D_531] :
      ( D_532 = D_531
      | k1_xboole_0 = D_531
      | k3_zfmisc_1(A_536,B_533,C_535) = k1_xboole_0
      | k4_zfmisc_1(A_536,B_533,C_535,D_531) != k2_zfmisc_1(C_534,D_532) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2901])).

tff(c_3036,plain,(
    ! [D_532,C_534] :
      ( D_532 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_534,D_532) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2790,c_3021])).

tff(c_3040,plain,(
    ! [D_532,C_534] :
      ( D_532 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_534,D_532) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_3036])).

tff(c_3041,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3040])).

tff(c_3063,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3041,c_8])).

tff(c_3074,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3063])).

tff(c_3076,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3074])).

tff(c_3096,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_30])).

tff(c_3095,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_26])).

tff(c_3094,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_24])).

tff(c_12,plain,(
    ! [A_9,C_11] : k3_zfmisc_1(A_9,k1_xboole_0,C_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2795,plain,(
    ! [A_477,B_478,C_479,D_480] : k2_zfmisc_1(k3_zfmisc_1(A_477,B_478,C_479),D_480) = k4_zfmisc_1(A_477,B_478,C_479,D_480) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2807,plain,(
    ! [A_9,C_11,D_480] : k4_zfmisc_1(A_9,k1_xboole_0,C_11,D_480) = k2_zfmisc_1(k1_xboole_0,D_480) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2795])).

tff(c_3087,plain,(
    ! [A_9,C_11,D_480] : k4_zfmisc_1(A_9,'#skF_6',C_11,D_480) = k2_zfmisc_1('#skF_6',D_480) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_3076,c_2807])).

tff(c_3165,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_zfmisc_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3087,c_2790])).

tff(c_2934,plain,(
    ! [D_507,A_510,B_508,B_511,A_512,C_509] :
      ( D_507 = B_511
      | k1_xboole_0 = B_511
      | k1_xboole_0 = A_512
      | k4_zfmisc_1(A_510,B_508,C_509,D_507) != k2_zfmisc_1(A_512,B_511) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2901])).

tff(c_2946,plain,(
    ! [D_507,A_510,B_508,B_2,C_3,A_1,D_4,C_509] :
      ( D_507 = D_4
      | k1_xboole_0 = D_4
      | k3_zfmisc_1(A_1,B_2,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_510,B_508,C_509,D_507) != k4_zfmisc_1(A_1,B_2,C_3,D_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2934])).

tff(c_3260,plain,(
    ! [B_563,D_564,D_561,A_566,C_565,B_562,C_567,A_560] :
      ( D_564 = D_561
      | D_561 = '#skF_6'
      | k3_zfmisc_1(A_566,B_563,C_565) = '#skF_6'
      | k4_zfmisc_1(A_566,B_563,C_565,D_561) != k4_zfmisc_1(A_560,B_562,C_567,D_564) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_3076,c_2946])).

tff(c_3269,plain,(
    ! [D_564,A_560,B_562,C_567] :
      ( D_564 = '#skF_4'
      | '#skF_6' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k4_zfmisc_1(A_560,B_562,C_567,D_564) != k2_zfmisc_1('#skF_6','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3165,c_3260])).

tff(c_3286,plain,(
    ! [D_564,A_560,B_562,C_567] :
      ( D_564 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k4_zfmisc_1(A_560,B_562,C_567,D_564) != k2_zfmisc_1('#skF_6','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3094,c_3269])).

tff(c_3327,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3286])).

tff(c_3089,plain,(
    ! [A_9,B_10,C_11] :
      ( k3_zfmisc_1(A_9,B_10,C_11) != '#skF_6'
      | C_11 = '#skF_6'
      | B_10 = '#skF_6'
      | A_9 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_3076,c_3076,c_3076,c_8])).

tff(c_3331,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3327,c_3089])).

tff(c_3340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3096,c_2789,c_3095,c_3331])).

tff(c_3342,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3286])).

tff(c_2890,plain,(
    ! [C_493,A_494,B_495,D_496] :
      ( C_493 = A_494
      | k1_xboole_0 = B_495
      | k1_xboole_0 = A_494
      | k2_zfmisc_1(C_493,D_496) != k2_zfmisc_1(A_494,B_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2896,plain,(
    ! [C_493,D_496,B_2,C_3,A_1,D_4] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = C_493
      | k1_xboole_0 = D_4
      | k3_zfmisc_1(A_1,B_2,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k2_zfmisc_1(C_493,D_496) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2890])).

tff(c_3101,plain,(
    ! [C_493,D_496,B_2,C_3,A_1,D_4] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = C_493
      | D_4 = '#skF_6'
      | k3_zfmisc_1(A_1,B_2,C_3) = '#skF_6'
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k2_zfmisc_1(C_493,D_496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3076,c_3076,c_2896])).

tff(c_3211,plain,(
    ! [C_493,D_496] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_493
      | '#skF_6' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k2_zfmisc_1(C_493,D_496) != k2_zfmisc_1('#skF_6','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3165,c_3101])).

tff(c_3214,plain,(
    ! [C_493,D_496] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_493
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k2_zfmisc_1(C_493,D_496) != k2_zfmisc_1('#skF_6','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3094,c_3211])).

tff(c_3380,plain,(
    ! [C_493,D_496] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_493
      | k2_zfmisc_1(C_493,D_496) != k2_zfmisc_1('#skF_6','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3342,c_3214])).

tff(c_3383,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3380])).

tff(c_3385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3342,c_3383])).

tff(c_3386,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3074])).

tff(c_3408,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3386,c_30])).

tff(c_3405,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3386,c_28])).

tff(c_3407,plain,(
    '#skF_7' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3386,c_26])).

tff(c_3406,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3386,c_24])).

tff(c_3066,plain,(
    ! [D_4] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_4) = k2_zfmisc_1(k1_xboole_0,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_3041,c_2])).

tff(c_3486,plain,(
    ! [D_4] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_4) = k2_zfmisc_1('#skF_7',D_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3386,c_3066])).

tff(c_3487,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_zfmisc_1('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3486,c_2790])).

tff(c_3598,plain,(
    ! [B_617,A_614,D_618,B_616,D_615,A_620,C_621,C_619] :
      ( D_618 = D_615
      | D_615 = '#skF_7'
      | k3_zfmisc_1(A_620,B_617,C_619) = '#skF_7'
      | k4_zfmisc_1(A_620,B_617,C_619,D_615) != k4_zfmisc_1(A_614,B_616,C_621,D_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3386,c_3386,c_2946])).

tff(c_3607,plain,(
    ! [D_618,A_614,B_616,C_621] :
      ( D_618 = '#skF_4'
      | '#skF_7' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k4_zfmisc_1(A_614,B_616,C_621,D_618) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3487,c_3598])).

tff(c_3624,plain,(
    ! [D_618,A_614,B_616,C_621] :
      ( D_618 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k4_zfmisc_1(A_614,B_616,C_621,D_618) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3406,c_3607])).

tff(c_3663,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3624])).

tff(c_3401,plain,(
    ! [A_9,B_10,C_11] :
      ( k3_zfmisc_1(A_9,B_10,C_11) != '#skF_7'
      | C_11 = '#skF_7'
      | B_10 = '#skF_7'
      | A_9 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3386,c_3386,c_3386,c_3386,c_8])).

tff(c_3667,plain,
    ( '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3663,c_3401])).

tff(c_3676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3408,c_3405,c_3407,c_3667])).

tff(c_3678,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3624])).

tff(c_3413,plain,(
    ! [C_493,D_496,B_2,C_3,A_1,D_4] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = C_493
      | D_4 = '#skF_7'
      | k3_zfmisc_1(A_1,B_2,C_3) = '#skF_7'
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k2_zfmisc_1(C_493,D_496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3386,c_3386,c_2896])).

tff(c_3547,plain,(
    ! [C_493,D_496] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_493
      | '#skF_7' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_493,D_496) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3487,c_3413])).

tff(c_3550,plain,(
    ! [C_493,D_496] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_493
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_493,D_496) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3406,c_3547])).

tff(c_3727,plain,(
    ! [C_493,D_496] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_493
      | k2_zfmisc_1(C_493,D_496) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3678,c_3550])).

tff(c_3730,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3727])).

tff(c_3732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3678,c_3730])).

tff(c_3734,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3040])).

tff(c_3794,plain,(
    ! [C_663,C_666,A_667,D_662,D_664,B_665] :
      ( k3_zfmisc_1(A_667,B_665,C_666) = C_663
      | k1_xboole_0 = D_664
      | k3_zfmisc_1(A_667,B_665,C_666) = k1_xboole_0
      | k4_zfmisc_1(A_667,B_665,C_666,D_664) != k2_zfmisc_1(C_663,D_662) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2890])).

tff(c_3809,plain,(
    ! [C_663,D_662] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = C_663
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_663,D_662) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2790,c_3794])).

tff(c_3814,plain,(
    ! [C_668,D_669] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = C_668
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_668,D_669) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3734,c_24,c_3809])).

tff(c_3817,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7')
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3814])).

tff(c_3820,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3817])).

tff(c_18,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13] :
      ( E_16 = B_13
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k3_zfmisc_1(D_15,E_16,F_17) != k3_zfmisc_1(A_12,B_13,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3851,plain,(
    ! [E_16,D_15,F_17] :
      ( E_16 = '#skF_6'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k3_zfmisc_1(D_15,E_16,F_17) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3820,c_18])).

tff(c_3872,plain,(
    ! [E_16,D_15,F_17] :
      ( E_16 = '#skF_6'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k3_zfmisc_1(D_15,E_16,F_17) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3851])).

tff(c_3926,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3872])).

tff(c_3844,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3820,c_3734])).

tff(c_3929,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3926,c_3844])).

tff(c_3945,plain,(
    ! [A_9,C_11] : k3_zfmisc_1(A_9,'#skF_6',C_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3926,c_3926,c_12])).

tff(c_3997,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3945,c_3820])).

tff(c_4025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3929,c_3997])).

tff(c_4026,plain,(
    ! [E_16,D_15,F_17] :
      ( k1_xboole_0 = '#skF_7'
      | E_16 = '#skF_6'
      | k3_zfmisc_1(D_15,E_16,F_17) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_3872])).

tff(c_4028,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_4026])).

tff(c_4032,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4028,c_3844])).

tff(c_4047,plain,(
    ! [A_9,B_10] : k3_zfmisc_1(A_9,B_10,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4028,c_4028,c_10])).

tff(c_4083,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4047,c_3820])).

tff(c_4129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4032,c_4083])).

tff(c_4130,plain,(
    ! [E_16,D_15,F_17] :
      ( E_16 = '#skF_6'
      | k3_zfmisc_1(D_15,E_16,F_17) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_4026])).

tff(c_4134,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4130])).

tff(c_4136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2789,c_4134])).

tff(c_4137,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2783])).

tff(c_4138,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2783])).

tff(c_4139,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1454,c_2784,c_32])).

tff(c_4144,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4138,c_4139])).

tff(c_4191,plain,(
    ! [D_716,B_717,A_718,C_719] :
      ( D_716 = B_717
      | k1_xboole_0 = B_717
      | k1_xboole_0 = A_718
      | k2_zfmisc_1(C_719,D_716) != k2_zfmisc_1(A_718,B_717) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4360,plain,(
    ! [D_757,C_760,B_759,A_762,D_758,C_761] :
      ( D_758 = D_757
      | k1_xboole_0 = D_758
      | k3_zfmisc_1(A_762,B_759,C_761) = k1_xboole_0
      | k4_zfmisc_1(A_762,B_759,C_761,D_758) != k2_zfmisc_1(C_760,D_757) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4191])).

tff(c_4375,plain,(
    ! [D_757,C_760] :
      ( D_757 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_760,D_757) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4144,c_4360])).

tff(c_4379,plain,(
    ! [D_757,C_760] :
      ( D_757 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_760,D_757) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_4375])).

tff(c_4399,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4379])).

tff(c_4424,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4399,c_8])).

tff(c_4432,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_4424])).

tff(c_4453,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4432,c_30])).

tff(c_4450,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4432,c_28])).

tff(c_4451,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4432,c_24])).

tff(c_4421,plain,(
    ! [D_4] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_4) = k2_zfmisc_1(k1_xboole_0,D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4399,c_2])).

tff(c_4543,plain,(
    ! [D_4] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_4) = k2_zfmisc_1('#skF_7',D_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4432,c_4421])).

tff(c_4544,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_zfmisc_1('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4543,c_4144])).

tff(c_4266,plain,(
    ! [B_736,A_733,C_737,D_734,B_735,A_738] :
      ( D_734 = B_736
      | k1_xboole_0 = B_736
      | k1_xboole_0 = A_733
      | k4_zfmisc_1(A_738,B_735,C_737,D_734) != k2_zfmisc_1(A_733,B_736) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4191])).

tff(c_4278,plain,(
    ! [B_2,C_3,A_1,C_737,D_4,D_734,B_735,A_738] :
      ( D_734 = D_4
      | k1_xboole_0 = D_4
      | k3_zfmisc_1(A_1,B_2,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_738,B_735,C_737,D_734) != k4_zfmisc_1(A_1,B_2,C_3,D_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4266])).

tff(c_4699,plain,(
    ! [A_816,B_810,D_812,C_817,D_813,C_815,B_814,A_811] :
      ( D_813 = D_812
      | D_812 = '#skF_7'
      | k3_zfmisc_1(A_816,B_814,C_815) = '#skF_7'
      | k4_zfmisc_1(A_816,B_814,C_815,D_812) != k4_zfmisc_1(A_811,B_810,C_817,D_813) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4432,c_4432,c_4278])).

tff(c_4714,plain,(
    ! [D_813,A_811,B_810,C_817] :
      ( D_813 = '#skF_4'
      | '#skF_7' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k4_zfmisc_1(A_811,B_810,C_817,D_813) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4544,c_4699])).

tff(c_4726,plain,(
    ! [D_813,A_811,B_810,C_817] :
      ( D_813 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k4_zfmisc_1(A_811,B_810,C_817,D_813) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4451,c_4714])).

tff(c_4728,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_4726])).

tff(c_4446,plain,(
    ! [A_9,B_10,C_11] :
      ( k3_zfmisc_1(A_9,B_10,C_11) != '#skF_7'
      | C_11 = '#skF_7'
      | B_10 = '#skF_7'
      | A_9 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4432,c_4432,c_4432,c_4432,c_8])).

tff(c_4732,plain,
    ( '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4728,c_4446])).

tff(c_4741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4453,c_4450,c_4137,c_4732])).

tff(c_4743,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4726])).

tff(c_4259,plain,(
    ! [C_729,A_730,B_731,D_732] :
      ( C_729 = A_730
      | k1_xboole_0 = B_731
      | k1_xboole_0 = A_730
      | k2_zfmisc_1(C_729,D_732) != k2_zfmisc_1(A_730,B_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4265,plain,(
    ! [B_2,C_3,A_1,D_4,C_729,D_732] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = C_729
      | k1_xboole_0 = D_4
      | k3_zfmisc_1(A_1,B_2,C_3) = k1_xboole_0
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k2_zfmisc_1(C_729,D_732) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4259])).

tff(c_4494,plain,(
    ! [B_2,C_3,A_1,D_4,C_729,D_732] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = C_729
      | D_4 = '#skF_7'
      | k3_zfmisc_1(A_1,B_2,C_3) = '#skF_7'
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k2_zfmisc_1(C_729,D_732) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4432,c_4432,c_4265])).

tff(c_4562,plain,(
    ! [C_729,D_732] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_729
      | '#skF_7' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_729,D_732) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4544,c_4494])).

tff(c_4565,plain,(
    ! [C_729,D_732] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_729
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_729,D_732) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4451,c_4562])).

tff(c_4744,plain,(
    ! [C_729,D_732] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_729
      | k2_zfmisc_1(C_729,D_732) != k2_zfmisc_1('#skF_7','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4743,c_4565])).

tff(c_4747,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4744])).

tff(c_4749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4743,c_4747])).

tff(c_4751,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4379])).

tff(c_4811,plain,(
    ! [A_838,D_835,B_836,C_834,C_837,D_839] :
      ( k3_zfmisc_1(A_838,B_836,C_837) = C_834
      | k1_xboole_0 = D_835
      | k3_zfmisc_1(A_838,B_836,C_837) = k1_xboole_0
      | k4_zfmisc_1(A_838,B_836,C_837,D_835) != k2_zfmisc_1(C_834,D_839) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4259])).

tff(c_4826,plain,(
    ! [C_834,D_839] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = C_834
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_834,D_839) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4144,c_4811])).

tff(c_4831,plain,(
    ! [C_840,D_841] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = C_840
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_840,D_841) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4751,c_24,c_4826])).

tff(c_4834,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( k3_zfmisc_1(A_1,B_2,C_3) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7')
      | k4_zfmisc_1(A_1,B_2,C_3,D_4) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4831])).

tff(c_4837,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4834])).

tff(c_16,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13] :
      ( F_17 = C_14
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k3_zfmisc_1(D_15,E_16,F_17) != k3_zfmisc_1(A_12,B_13,C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4874,plain,(
    ! [F_17,D_15,E_16] :
      ( F_17 = '#skF_7'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1'
      | k3_zfmisc_1(D_15,E_16,F_17) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4837,c_16])).

tff(c_4890,plain,(
    ! [F_17,D_15,E_16] :
      ( F_17 = '#skF_7'
      | k1_xboole_0 = '#skF_7'
      | k3_zfmisc_1(D_15,E_16,F_17) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_4874])).

tff(c_4935,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_4890])).

tff(c_4861,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4837,c_4751])).

tff(c_4937,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4935,c_4861])).

tff(c_4952,plain,(
    ! [A_9,B_10] : k3_zfmisc_1(A_9,B_10,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4935,c_4935,c_10])).

tff(c_4991,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4952,c_4837])).

tff(c_5032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4937,c_4991])).

tff(c_5033,plain,(
    ! [F_17,D_15,E_16] :
      ( F_17 = '#skF_7'
      | k3_zfmisc_1(D_15,E_16,F_17) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_4890])).

tff(c_5057,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5033])).

tff(c_5059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4137,c_5057])).

%------------------------------------------------------------------------------
