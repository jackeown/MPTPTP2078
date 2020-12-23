%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:39 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 6.07s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 179 expanded)
%              Number of leaves         :   26 (  80 expanded)
%              Depth                    :    8
%              Number of atoms          :  241 ( 668 expanded)
%              Number of equality atoms :  198 ( 540 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                  & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                  & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ! [G] :
                        ( m1_subset_1(G,C)
                       => D != k3_mcart_1(E,F,G) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ? [E,F,G] :
                ( D = k3_mcart_1(E,F,G)
                & ~ ( k5_mcart_1(A,B,C,D) = E
                    & k6_mcart_1(A,B,C,D) = F
                    & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_mcart_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2339,plain,(
    ! [A_614,B_615,C_616,D_617] :
      ( k3_mcart_1('#skF_1'(A_614,B_615,C_616,D_617),'#skF_2'(A_614,B_615,C_616,D_617),'#skF_3'(A_614,B_615,C_616,D_617)) = D_617
      | ~ m1_subset_1(D_617,k3_zfmisc_1(A_614,B_615,C_616))
      | k1_xboole_0 = C_616
      | k1_xboole_0 = B_615
      | k1_xboole_0 = A_614 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,(
    ! [A_64,B_65,C_66] : k4_tarski(k4_tarski(A_64,B_65),C_66) = k3_mcart_1(A_64,B_65,C_66) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_54,B_55] : k1_mcart_1(k4_tarski(A_54,B_55)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_75,plain,(
    ! [A_64,B_65,C_66] : k1_mcart_1(k3_mcart_1(A_64,B_65,C_66)) = k4_tarski(A_64,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_20])).

tff(c_2400,plain,(
    ! [A_622,B_623,C_624,D_625] :
      ( k4_tarski('#skF_1'(A_622,B_623,C_624,D_625),'#skF_2'(A_622,B_623,C_624,D_625)) = k1_mcart_1(D_625)
      | ~ m1_subset_1(D_625,k3_zfmisc_1(A_622,B_623,C_624))
      | k1_xboole_0 = C_624
      | k1_xboole_0 = B_623
      | k1_xboole_0 = A_622 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2339,c_75])).

tff(c_22,plain,(
    ! [A_54,B_55] : k2_mcart_1(k4_tarski(A_54,B_55)) = B_55 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2470,plain,(
    ! [D_637,A_638,B_639,C_640] :
      ( k2_mcart_1(k1_mcart_1(D_637)) = '#skF_2'(A_638,B_639,C_640,D_637)
      | ~ m1_subset_1(D_637,k3_zfmisc_1(A_638,B_639,C_640))
      | k1_xboole_0 = C_640
      | k1_xboole_0 = B_639
      | k1_xboole_0 = A_638 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2400,c_22])).

tff(c_2488,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_2470])).

tff(c_2494,plain,(
    k2_mcart_1(k1_mcart_1('#skF_7')) = '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_2488])).

tff(c_1323,plain,(
    ! [A_393,B_394,C_395,D_396] :
      ( k3_mcart_1('#skF_1'(A_393,B_394,C_395,D_396),'#skF_2'(A_393,B_394,C_395,D_396),'#skF_3'(A_393,B_394,C_395,D_396)) = D_396
      | ~ m1_subset_1(D_396,k3_zfmisc_1(A_393,B_394,C_395))
      | k1_xboole_0 = C_395
      | k1_xboole_0 = B_394
      | k1_xboole_0 = A_393 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_78,plain,(
    ! [A_64,B_65,C_66] : k2_mcart_1(k3_mcart_1(A_64,B_65,C_66)) = C_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_22])).

tff(c_1353,plain,(
    ! [D_397,A_398,B_399,C_400] :
      ( k2_mcart_1(D_397) = '#skF_3'(A_398,B_399,C_400,D_397)
      | ~ m1_subset_1(D_397,k3_zfmisc_1(A_398,B_399,C_400))
      | k1_xboole_0 = C_400
      | k1_xboole_0 = B_399
      | k1_xboole_0 = A_398 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1323,c_78])).

tff(c_1371,plain,
    ( k2_mcart_1('#skF_7') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_1353])).

tff(c_1377,plain,(
    k2_mcart_1('#skF_7') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_1371])).

tff(c_191,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( k3_mcart_1('#skF_1'(A_125,B_126,C_127,D_128),'#skF_2'(A_125,B_126,C_127,D_128),'#skF_3'(A_125,B_126,C_127,D_128)) = D_128
      | ~ m1_subset_1(D_128,k3_zfmisc_1(A_125,B_126,C_127))
      | k1_xboole_0 = C_127
      | k1_xboole_0 = B_126
      | k1_xboole_0 = A_125 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_268,plain,(
    ! [A_140,B_141,C_142,D_143] :
      ( k4_tarski('#skF_1'(A_140,B_141,C_142,D_143),'#skF_2'(A_140,B_141,C_142,D_143)) = k1_mcart_1(D_143)
      | ~ m1_subset_1(D_143,k3_zfmisc_1(A_140,B_141,C_142))
      | k1_xboole_0 = C_142
      | k1_xboole_0 = B_141
      | k1_xboole_0 = A_140 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_75])).

tff(c_289,plain,(
    ! [D_144,A_145,B_146,C_147] :
      ( k1_mcart_1(k1_mcart_1(D_144)) = '#skF_1'(A_145,B_146,C_147,D_144)
      | ~ m1_subset_1(D_144,k3_zfmisc_1(A_145,B_146,C_147))
      | k1_xboole_0 = C_147
      | k1_xboole_0 = B_146
      | k1_xboole_0 = A_145 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_20])).

tff(c_307,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = '#skF_1'('#skF_4','#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_289])).

tff(c_313,plain,(
    k1_mcart_1(k1_mcart_1('#skF_7')) = '#skF_1'('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_307])).

tff(c_24,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') != k2_mcart_1('#skF_7')
    | k2_mcart_1(k1_mcart_1('#skF_7')) != k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')
    | k1_mcart_1(k1_mcart_1('#skF_7')) != k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_96,plain,(
    k1_mcart_1(k1_mcart_1('#skF_7')) != k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_314,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') != '#skF_1'('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_96])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( k3_mcart_1('#skF_1'(A_7,B_8,C_9,D_25),'#skF_2'(A_7,B_8,C_9,D_25),'#skF_3'(A_7,B_8,C_9,D_25)) = D_25
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [C_39,B_38,G_53,F_52,E_51,A_37] :
      ( k5_mcart_1(A_37,B_38,C_39,k3_mcart_1(E_51,F_52,G_53)) = E_51
      | ~ m1_subset_1(k3_mcart_1(E_51,F_52,G_53),k3_zfmisc_1(A_37,B_38,C_39))
      | k1_xboole_0 = C_39
      | k1_xboole_0 = B_38
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_627,plain,(
    ! [D_220,C_221,A_217,A_222,B_218,B_223,C_219] :
      ( k5_mcart_1(A_217,B_218,C_221,k3_mcart_1('#skF_1'(A_222,B_223,C_219,D_220),'#skF_2'(A_222,B_223,C_219,D_220),'#skF_3'(A_222,B_223,C_219,D_220))) = '#skF_1'(A_222,B_223,C_219,D_220)
      | ~ m1_subset_1(D_220,k3_zfmisc_1(A_217,B_218,C_221))
      | k1_xboole_0 = C_221
      | k1_xboole_0 = B_218
      | k1_xboole_0 = A_217
      | ~ m1_subset_1(D_220,k3_zfmisc_1(A_222,B_223,C_219))
      | k1_xboole_0 = C_219
      | k1_xboole_0 = B_223
      | k1_xboole_0 = A_222 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_18])).

tff(c_1191,plain,(
    ! [A_331,C_328,C_330,B_329,A_333,B_332,D_334] :
      ( k5_mcart_1(A_333,B_332,C_328,D_334) = '#skF_1'(A_331,B_329,C_330,D_334)
      | ~ m1_subset_1(D_334,k3_zfmisc_1(A_333,B_332,C_328))
      | k1_xboole_0 = C_328
      | k1_xboole_0 = B_332
      | k1_xboole_0 = A_333
      | ~ m1_subset_1(D_334,k3_zfmisc_1(A_331,B_329,C_330))
      | k1_xboole_0 = C_330
      | k1_xboole_0 = B_329
      | k1_xboole_0 = A_331
      | ~ m1_subset_1(D_334,k3_zfmisc_1(A_331,B_329,C_330))
      | k1_xboole_0 = C_330
      | k1_xboole_0 = B_329
      | k1_xboole_0 = A_331 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_627])).

tff(c_1204,plain,(
    ! [A_331,B_329,C_330] :
      ( k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_1'(A_331,B_329,C_330,'#skF_7')
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_331,B_329,C_330))
      | k1_xboole_0 = C_330
      | k1_xboole_0 = B_329
      | k1_xboole_0 = A_331 ) ),
    inference(resolution,[status(thm)],[c_26,c_1191])).

tff(c_1211,plain,(
    ! [A_335,B_336,C_337] :
      ( k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_1'(A_335,B_336,C_337,'#skF_7')
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_335,B_336,C_337))
      | k1_xboole_0 = C_337
      | k1_xboole_0 = B_336
      | k1_xboole_0 = A_335 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_1204])).

tff(c_1217,plain,
    ( k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_1'('#skF_4','#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_1211])).

tff(c_1221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_314,c_1217])).

tff(c_1222,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) != k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') != k2_mcart_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1237,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') != k2_mcart_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1222])).

tff(c_1393,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') != '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_1237])).

tff(c_14,plain,(
    ! [C_39,B_38,G_53,F_52,E_51,A_37] :
      ( k7_mcart_1(A_37,B_38,C_39,k3_mcart_1(E_51,F_52,G_53)) = G_53
      | ~ m1_subset_1(k3_mcart_1(E_51,F_52,G_53),k3_zfmisc_1(A_37,B_38,C_39))
      | k1_xboole_0 = C_39
      | k1_xboole_0 = B_38
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1509,plain,(
    ! [C_427,C_430,D_429,A_425,B_428,A_431,B_426] :
      ( k7_mcart_1(A_425,B_426,C_427,k3_mcart_1('#skF_1'(A_431,B_428,C_430,D_429),'#skF_2'(A_431,B_428,C_430,D_429),'#skF_3'(A_431,B_428,C_430,D_429))) = '#skF_3'(A_431,B_428,C_430,D_429)
      | ~ m1_subset_1(D_429,k3_zfmisc_1(A_425,B_426,C_427))
      | k1_xboole_0 = C_427
      | k1_xboole_0 = B_426
      | k1_xboole_0 = A_425
      | ~ m1_subset_1(D_429,k3_zfmisc_1(A_431,B_428,C_430))
      | k1_xboole_0 = C_430
      | k1_xboole_0 = B_428
      | k1_xboole_0 = A_431 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1323,c_14])).

tff(c_2233,plain,(
    ! [C_569,B_568,C_572,D_571,A_567,A_570,B_566] :
      ( k7_mcart_1(A_567,B_566,C_572,D_571) = '#skF_3'(A_570,B_568,C_569,D_571)
      | ~ m1_subset_1(D_571,k3_zfmisc_1(A_567,B_566,C_572))
      | k1_xboole_0 = C_572
      | k1_xboole_0 = B_566
      | k1_xboole_0 = A_567
      | ~ m1_subset_1(D_571,k3_zfmisc_1(A_570,B_568,C_569))
      | k1_xboole_0 = C_569
      | k1_xboole_0 = B_568
      | k1_xboole_0 = A_570
      | ~ m1_subset_1(D_571,k3_zfmisc_1(A_570,B_568,C_569))
      | k1_xboole_0 = C_569
      | k1_xboole_0 = B_568
      | k1_xboole_0 = A_570 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1509])).

tff(c_2246,plain,(
    ! [A_570,B_568,C_569] :
      ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_3'(A_570,B_568,C_569,'#skF_7')
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_570,B_568,C_569))
      | k1_xboole_0 = C_569
      | k1_xboole_0 = B_568
      | k1_xboole_0 = A_570 ) ),
    inference(resolution,[status(thm)],[c_26,c_2233])).

tff(c_2253,plain,(
    ! [A_573,B_574,C_575] :
      ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_3'(A_573,B_574,C_575,'#skF_7')
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_573,B_574,C_575))
      | k1_xboole_0 = C_575
      | k1_xboole_0 = B_574
      | k1_xboole_0 = A_573 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_2246])).

tff(c_2259,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_2253])).

tff(c_2263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_1393,c_2259])).

tff(c_2264,plain,(
    k2_mcart_1(k1_mcart_1('#skF_7')) != k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1222])).

tff(c_2495,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') != '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2494,c_2264])).

tff(c_16,plain,(
    ! [C_39,B_38,G_53,F_52,E_51,A_37] :
      ( k6_mcart_1(A_37,B_38,C_39,k3_mcart_1(E_51,F_52,G_53)) = F_52
      | ~ m1_subset_1(k3_mcart_1(E_51,F_52,G_53),k3_zfmisc_1(A_37,B_38,C_39))
      | k1_xboole_0 = C_39
      | k1_xboole_0 = B_38
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2577,plain,(
    ! [D_667,C_666,B_664,A_663,B_669,C_665,A_668] :
      ( k6_mcart_1(A_663,B_664,C_666,k3_mcart_1('#skF_1'(A_668,B_669,C_665,D_667),'#skF_2'(A_668,B_669,C_665,D_667),'#skF_3'(A_668,B_669,C_665,D_667))) = '#skF_2'(A_668,B_669,C_665,D_667)
      | ~ m1_subset_1(D_667,k3_zfmisc_1(A_663,B_664,C_666))
      | k1_xboole_0 = C_666
      | k1_xboole_0 = B_664
      | k1_xboole_0 = A_663
      | ~ m1_subset_1(D_667,k3_zfmisc_1(A_668,B_669,C_665))
      | k1_xboole_0 = C_665
      | k1_xboole_0 = B_669
      | k1_xboole_0 = A_668 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2339,c_16])).

tff(c_3289,plain,(
    ! [A_809,B_807,D_812,C_806,B_811,A_810,C_808] :
      ( k6_mcart_1(A_810,B_811,C_806,D_812) = '#skF_2'(A_809,B_807,C_808,D_812)
      | ~ m1_subset_1(D_812,k3_zfmisc_1(A_810,B_811,C_806))
      | k1_xboole_0 = C_806
      | k1_xboole_0 = B_811
      | k1_xboole_0 = A_810
      | ~ m1_subset_1(D_812,k3_zfmisc_1(A_809,B_807,C_808))
      | k1_xboole_0 = C_808
      | k1_xboole_0 = B_807
      | k1_xboole_0 = A_809
      | ~ m1_subset_1(D_812,k3_zfmisc_1(A_809,B_807,C_808))
      | k1_xboole_0 = C_808
      | k1_xboole_0 = B_807
      | k1_xboole_0 = A_809 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2577])).

tff(c_3302,plain,(
    ! [A_809,B_807,C_808] :
      ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_2'(A_809,B_807,C_808,'#skF_7')
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_809,B_807,C_808))
      | k1_xboole_0 = C_808
      | k1_xboole_0 = B_807
      | k1_xboole_0 = A_809 ) ),
    inference(resolution,[status(thm)],[c_26,c_3289])).

tff(c_3309,plain,(
    ! [A_813,B_814,C_815] :
      ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_2'(A_813,B_814,C_815,'#skF_7')
      | ~ m1_subset_1('#skF_7',k3_zfmisc_1(A_813,B_814,C_815))
      | k1_xboole_0 = C_815
      | k1_xboole_0 = B_814
      | k1_xboole_0 = A_813 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_3302])).

tff(c_3315,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_3309])).

tff(c_3319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_2495,c_3315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.34  % CPULimit   : 60
% 0.18/0.34  % DateTime   : Tue Dec  1 09:57:47 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.10  
% 5.93/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.10  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 5.93/2.10  
% 5.93/2.10  %Foreground sorts:
% 5.93/2.10  
% 5.93/2.10  
% 5.93/2.10  %Background operators:
% 5.93/2.10  
% 5.93/2.10  
% 5.93/2.10  %Foreground operators:
% 5.93/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.93/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.93/2.10  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.93/2.10  tff('#skF_7', type, '#skF_7': $i).
% 5.93/2.10  tff('#skF_5', type, '#skF_5': $i).
% 5.93/2.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.93/2.10  tff('#skF_6', type, '#skF_6': $i).
% 5.93/2.10  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 5.93/2.10  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.93/2.10  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 5.93/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.10  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.93/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.93/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.93/2.10  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 5.93/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.10  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.93/2.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.93/2.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.93/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.93/2.10  
% 6.07/2.12  tff(f_102, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 6.07/2.12  tff(f_54, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 6.07/2.12  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 6.07/2.12  tff(f_81, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 6.07/2.12  tff(f_77, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_mcart_1)).
% 6.07/2.12  tff(c_32, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.07/2.12  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.07/2.12  tff(c_28, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.07/2.12  tff(c_26, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.07/2.12  tff(c_2339, plain, (![A_614, B_615, C_616, D_617]: (k3_mcart_1('#skF_1'(A_614, B_615, C_616, D_617), '#skF_2'(A_614, B_615, C_616, D_617), '#skF_3'(A_614, B_615, C_616, D_617))=D_617 | ~m1_subset_1(D_617, k3_zfmisc_1(A_614, B_615, C_616)) | k1_xboole_0=C_616 | k1_xboole_0=B_615 | k1_xboole_0=A_614)), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.07/2.12  tff(c_66, plain, (![A_64, B_65, C_66]: (k4_tarski(k4_tarski(A_64, B_65), C_66)=k3_mcart_1(A_64, B_65, C_66))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.07/2.12  tff(c_20, plain, (![A_54, B_55]: (k1_mcart_1(k4_tarski(A_54, B_55))=A_54)), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.07/2.12  tff(c_75, plain, (![A_64, B_65, C_66]: (k1_mcart_1(k3_mcart_1(A_64, B_65, C_66))=k4_tarski(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_66, c_20])).
% 6.07/2.12  tff(c_2400, plain, (![A_622, B_623, C_624, D_625]: (k4_tarski('#skF_1'(A_622, B_623, C_624, D_625), '#skF_2'(A_622, B_623, C_624, D_625))=k1_mcart_1(D_625) | ~m1_subset_1(D_625, k3_zfmisc_1(A_622, B_623, C_624)) | k1_xboole_0=C_624 | k1_xboole_0=B_623 | k1_xboole_0=A_622)), inference(superposition, [status(thm), theory('equality')], [c_2339, c_75])).
% 6.07/2.12  tff(c_22, plain, (![A_54, B_55]: (k2_mcart_1(k4_tarski(A_54, B_55))=B_55)), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.07/2.12  tff(c_2470, plain, (![D_637, A_638, B_639, C_640]: (k2_mcart_1(k1_mcart_1(D_637))='#skF_2'(A_638, B_639, C_640, D_637) | ~m1_subset_1(D_637, k3_zfmisc_1(A_638, B_639, C_640)) | k1_xboole_0=C_640 | k1_xboole_0=B_639 | k1_xboole_0=A_638)), inference(superposition, [status(thm), theory('equality')], [c_2400, c_22])).
% 6.07/2.12  tff(c_2488, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_26, c_2470])).
% 6.07/2.12  tff(c_2494, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_2488])).
% 6.07/2.12  tff(c_1323, plain, (![A_393, B_394, C_395, D_396]: (k3_mcart_1('#skF_1'(A_393, B_394, C_395, D_396), '#skF_2'(A_393, B_394, C_395, D_396), '#skF_3'(A_393, B_394, C_395, D_396))=D_396 | ~m1_subset_1(D_396, k3_zfmisc_1(A_393, B_394, C_395)) | k1_xboole_0=C_395 | k1_xboole_0=B_394 | k1_xboole_0=A_393)), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.07/2.12  tff(c_78, plain, (![A_64, B_65, C_66]: (k2_mcart_1(k3_mcart_1(A_64, B_65, C_66))=C_66)), inference(superposition, [status(thm), theory('equality')], [c_66, c_22])).
% 6.07/2.12  tff(c_1353, plain, (![D_397, A_398, B_399, C_400]: (k2_mcart_1(D_397)='#skF_3'(A_398, B_399, C_400, D_397) | ~m1_subset_1(D_397, k3_zfmisc_1(A_398, B_399, C_400)) | k1_xboole_0=C_400 | k1_xboole_0=B_399 | k1_xboole_0=A_398)), inference(superposition, [status(thm), theory('equality')], [c_1323, c_78])).
% 6.07/2.12  tff(c_1371, plain, (k2_mcart_1('#skF_7')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_26, c_1353])).
% 6.07/2.12  tff(c_1377, plain, (k2_mcart_1('#skF_7')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_1371])).
% 6.07/2.12  tff(c_191, plain, (![A_125, B_126, C_127, D_128]: (k3_mcart_1('#skF_1'(A_125, B_126, C_127, D_128), '#skF_2'(A_125, B_126, C_127, D_128), '#skF_3'(A_125, B_126, C_127, D_128))=D_128 | ~m1_subset_1(D_128, k3_zfmisc_1(A_125, B_126, C_127)) | k1_xboole_0=C_127 | k1_xboole_0=B_126 | k1_xboole_0=A_125)), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.07/2.12  tff(c_268, plain, (![A_140, B_141, C_142, D_143]: (k4_tarski('#skF_1'(A_140, B_141, C_142, D_143), '#skF_2'(A_140, B_141, C_142, D_143))=k1_mcart_1(D_143) | ~m1_subset_1(D_143, k3_zfmisc_1(A_140, B_141, C_142)) | k1_xboole_0=C_142 | k1_xboole_0=B_141 | k1_xboole_0=A_140)), inference(superposition, [status(thm), theory('equality')], [c_191, c_75])).
% 6.07/2.12  tff(c_289, plain, (![D_144, A_145, B_146, C_147]: (k1_mcart_1(k1_mcart_1(D_144))='#skF_1'(A_145, B_146, C_147, D_144) | ~m1_subset_1(D_144, k3_zfmisc_1(A_145, B_146, C_147)) | k1_xboole_0=C_147 | k1_xboole_0=B_146 | k1_xboole_0=A_145)), inference(superposition, [status(thm), theory('equality')], [c_268, c_20])).
% 6.07/2.12  tff(c_307, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))='#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_26, c_289])).
% 6.07/2.12  tff(c_313, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))='#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_307])).
% 6.07/2.12  tff(c_24, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k2_mcart_1('#skF_7') | k2_mcart_1(k1_mcart_1('#skF_7'))!=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7') | k1_mcart_1(k1_mcart_1('#skF_7'))!=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.07/2.12  tff(c_96, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))!=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_24])).
% 6.07/2.12  tff(c_314, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')!='#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_96])).
% 6.07/2.12  tff(c_6, plain, (![A_7, B_8, C_9, D_25]: (k3_mcart_1('#skF_1'(A_7, B_8, C_9, D_25), '#skF_2'(A_7, B_8, C_9, D_25), '#skF_3'(A_7, B_8, C_9, D_25))=D_25 | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.07/2.12  tff(c_18, plain, (![C_39, B_38, G_53, F_52, E_51, A_37]: (k5_mcart_1(A_37, B_38, C_39, k3_mcart_1(E_51, F_52, G_53))=E_51 | ~m1_subset_1(k3_mcart_1(E_51, F_52, G_53), k3_zfmisc_1(A_37, B_38, C_39)) | k1_xboole_0=C_39 | k1_xboole_0=B_38 | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.07/2.12  tff(c_627, plain, (![D_220, C_221, A_217, A_222, B_218, B_223, C_219]: (k5_mcart_1(A_217, B_218, C_221, k3_mcart_1('#skF_1'(A_222, B_223, C_219, D_220), '#skF_2'(A_222, B_223, C_219, D_220), '#skF_3'(A_222, B_223, C_219, D_220)))='#skF_1'(A_222, B_223, C_219, D_220) | ~m1_subset_1(D_220, k3_zfmisc_1(A_217, B_218, C_221)) | k1_xboole_0=C_221 | k1_xboole_0=B_218 | k1_xboole_0=A_217 | ~m1_subset_1(D_220, k3_zfmisc_1(A_222, B_223, C_219)) | k1_xboole_0=C_219 | k1_xboole_0=B_223 | k1_xboole_0=A_222)), inference(superposition, [status(thm), theory('equality')], [c_191, c_18])).
% 6.07/2.12  tff(c_1191, plain, (![A_331, C_328, C_330, B_329, A_333, B_332, D_334]: (k5_mcart_1(A_333, B_332, C_328, D_334)='#skF_1'(A_331, B_329, C_330, D_334) | ~m1_subset_1(D_334, k3_zfmisc_1(A_333, B_332, C_328)) | k1_xboole_0=C_328 | k1_xboole_0=B_332 | k1_xboole_0=A_333 | ~m1_subset_1(D_334, k3_zfmisc_1(A_331, B_329, C_330)) | k1_xboole_0=C_330 | k1_xboole_0=B_329 | k1_xboole_0=A_331 | ~m1_subset_1(D_334, k3_zfmisc_1(A_331, B_329, C_330)) | k1_xboole_0=C_330 | k1_xboole_0=B_329 | k1_xboole_0=A_331)), inference(superposition, [status(thm), theory('equality')], [c_6, c_627])).
% 6.07/2.12  tff(c_1204, plain, (![A_331, B_329, C_330]: (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_1'(A_331, B_329, C_330, '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_331, B_329, C_330)) | k1_xboole_0=C_330 | k1_xboole_0=B_329 | k1_xboole_0=A_331)), inference(resolution, [status(thm)], [c_26, c_1191])).
% 6.07/2.12  tff(c_1211, plain, (![A_335, B_336, C_337]: (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_1'(A_335, B_336, C_337, '#skF_7') | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_335, B_336, C_337)) | k1_xboole_0=C_337 | k1_xboole_0=B_336 | k1_xboole_0=A_335)), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_1204])).
% 6.07/2.12  tff(c_1217, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_26, c_1211])).
% 6.07/2.12  tff(c_1221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_314, c_1217])).
% 6.07/2.12  tff(c_1222, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))!=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7') | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k2_mcart_1('#skF_7')), inference(splitRight, [status(thm)], [c_24])).
% 6.07/2.12  tff(c_1237, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k2_mcart_1('#skF_7')), inference(splitLeft, [status(thm)], [c_1222])).
% 6.07/2.12  tff(c_1393, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')!='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_1237])).
% 6.07/2.12  tff(c_14, plain, (![C_39, B_38, G_53, F_52, E_51, A_37]: (k7_mcart_1(A_37, B_38, C_39, k3_mcart_1(E_51, F_52, G_53))=G_53 | ~m1_subset_1(k3_mcart_1(E_51, F_52, G_53), k3_zfmisc_1(A_37, B_38, C_39)) | k1_xboole_0=C_39 | k1_xboole_0=B_38 | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.07/2.12  tff(c_1509, plain, (![C_427, C_430, D_429, A_425, B_428, A_431, B_426]: (k7_mcart_1(A_425, B_426, C_427, k3_mcart_1('#skF_1'(A_431, B_428, C_430, D_429), '#skF_2'(A_431, B_428, C_430, D_429), '#skF_3'(A_431, B_428, C_430, D_429)))='#skF_3'(A_431, B_428, C_430, D_429) | ~m1_subset_1(D_429, k3_zfmisc_1(A_425, B_426, C_427)) | k1_xboole_0=C_427 | k1_xboole_0=B_426 | k1_xboole_0=A_425 | ~m1_subset_1(D_429, k3_zfmisc_1(A_431, B_428, C_430)) | k1_xboole_0=C_430 | k1_xboole_0=B_428 | k1_xboole_0=A_431)), inference(superposition, [status(thm), theory('equality')], [c_1323, c_14])).
% 6.07/2.12  tff(c_2233, plain, (![C_569, B_568, C_572, D_571, A_567, A_570, B_566]: (k7_mcart_1(A_567, B_566, C_572, D_571)='#skF_3'(A_570, B_568, C_569, D_571) | ~m1_subset_1(D_571, k3_zfmisc_1(A_567, B_566, C_572)) | k1_xboole_0=C_572 | k1_xboole_0=B_566 | k1_xboole_0=A_567 | ~m1_subset_1(D_571, k3_zfmisc_1(A_570, B_568, C_569)) | k1_xboole_0=C_569 | k1_xboole_0=B_568 | k1_xboole_0=A_570 | ~m1_subset_1(D_571, k3_zfmisc_1(A_570, B_568, C_569)) | k1_xboole_0=C_569 | k1_xboole_0=B_568 | k1_xboole_0=A_570)), inference(superposition, [status(thm), theory('equality')], [c_6, c_1509])).
% 6.07/2.12  tff(c_2246, plain, (![A_570, B_568, C_569]: (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_3'(A_570, B_568, C_569, '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_570, B_568, C_569)) | k1_xboole_0=C_569 | k1_xboole_0=B_568 | k1_xboole_0=A_570)), inference(resolution, [status(thm)], [c_26, c_2233])).
% 6.07/2.12  tff(c_2253, plain, (![A_573, B_574, C_575]: (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_3'(A_573, B_574, C_575, '#skF_7') | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_573, B_574, C_575)) | k1_xboole_0=C_575 | k1_xboole_0=B_574 | k1_xboole_0=A_573)), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_2246])).
% 6.07/2.12  tff(c_2259, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_26, c_2253])).
% 6.07/2.12  tff(c_2263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_1393, c_2259])).
% 6.07/2.12  tff(c_2264, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))!=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_1222])).
% 6.07/2.12  tff(c_2495, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')!='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2494, c_2264])).
% 6.07/2.12  tff(c_16, plain, (![C_39, B_38, G_53, F_52, E_51, A_37]: (k6_mcart_1(A_37, B_38, C_39, k3_mcart_1(E_51, F_52, G_53))=F_52 | ~m1_subset_1(k3_mcart_1(E_51, F_52, G_53), k3_zfmisc_1(A_37, B_38, C_39)) | k1_xboole_0=C_39 | k1_xboole_0=B_38 | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.07/2.12  tff(c_2577, plain, (![D_667, C_666, B_664, A_663, B_669, C_665, A_668]: (k6_mcart_1(A_663, B_664, C_666, k3_mcart_1('#skF_1'(A_668, B_669, C_665, D_667), '#skF_2'(A_668, B_669, C_665, D_667), '#skF_3'(A_668, B_669, C_665, D_667)))='#skF_2'(A_668, B_669, C_665, D_667) | ~m1_subset_1(D_667, k3_zfmisc_1(A_663, B_664, C_666)) | k1_xboole_0=C_666 | k1_xboole_0=B_664 | k1_xboole_0=A_663 | ~m1_subset_1(D_667, k3_zfmisc_1(A_668, B_669, C_665)) | k1_xboole_0=C_665 | k1_xboole_0=B_669 | k1_xboole_0=A_668)), inference(superposition, [status(thm), theory('equality')], [c_2339, c_16])).
% 6.07/2.12  tff(c_3289, plain, (![A_809, B_807, D_812, C_806, B_811, A_810, C_808]: (k6_mcart_1(A_810, B_811, C_806, D_812)='#skF_2'(A_809, B_807, C_808, D_812) | ~m1_subset_1(D_812, k3_zfmisc_1(A_810, B_811, C_806)) | k1_xboole_0=C_806 | k1_xboole_0=B_811 | k1_xboole_0=A_810 | ~m1_subset_1(D_812, k3_zfmisc_1(A_809, B_807, C_808)) | k1_xboole_0=C_808 | k1_xboole_0=B_807 | k1_xboole_0=A_809 | ~m1_subset_1(D_812, k3_zfmisc_1(A_809, B_807, C_808)) | k1_xboole_0=C_808 | k1_xboole_0=B_807 | k1_xboole_0=A_809)), inference(superposition, [status(thm), theory('equality')], [c_6, c_2577])).
% 6.07/2.12  tff(c_3302, plain, (![A_809, B_807, C_808]: (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_2'(A_809, B_807, C_808, '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_809, B_807, C_808)) | k1_xboole_0=C_808 | k1_xboole_0=B_807 | k1_xboole_0=A_809)), inference(resolution, [status(thm)], [c_26, c_3289])).
% 6.07/2.12  tff(c_3309, plain, (![A_813, B_814, C_815]: (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_2'(A_813, B_814, C_815, '#skF_7') | ~m1_subset_1('#skF_7', k3_zfmisc_1(A_813, B_814, C_815)) | k1_xboole_0=C_815 | k1_xboole_0=B_814 | k1_xboole_0=A_813)), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_3302])).
% 6.07/2.12  tff(c_3315, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_26, c_3309])).
% 6.07/2.12  tff(c_3319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_2495, c_3315])).
% 6.07/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.12  
% 6.07/2.12  Inference rules
% 6.07/2.12  ----------------------
% 6.07/2.12  #Ref     : 0
% 6.07/2.12  #Sup     : 803
% 6.07/2.12  #Fact    : 0
% 6.07/2.12  #Define  : 0
% 6.07/2.12  #Split   : 2
% 6.07/2.12  #Chain   : 0
% 6.07/2.12  #Close   : 0
% 6.07/2.12  
% 6.07/2.12  Ordering : KBO
% 6.07/2.12  
% 6.07/2.12  Simplification rules
% 6.07/2.12  ----------------------
% 6.07/2.12  #Subsume      : 93
% 6.07/2.12  #Demod        : 393
% 6.07/2.12  #Tautology    : 208
% 6.07/2.12  #SimpNegUnit  : 25
% 6.07/2.12  #BackRed      : 8
% 6.07/2.12  
% 6.07/2.12  #Partial instantiations: 0
% 6.07/2.12  #Strategies tried      : 1
% 6.07/2.12  
% 6.07/2.12  Timing (in seconds)
% 6.07/2.12  ----------------------
% 6.07/2.12  Preprocessing        : 0.31
% 6.07/2.12  Parsing              : 0.16
% 6.07/2.12  CNF conversion       : 0.02
% 6.07/2.12  Main loop            : 1.09
% 6.07/2.13  Inferencing          : 0.45
% 6.07/2.13  Reduction            : 0.28
% 6.07/2.13  Demodulation         : 0.20
% 6.07/2.13  BG Simplification    : 0.07
% 6.07/2.13  Subsumption          : 0.21
% 6.07/2.13  Abstraction          : 0.10
% 6.07/2.13  MUC search           : 0.00
% 6.07/2.13  Cooper               : 0.00
% 6.07/2.13  Total                : 1.43
% 6.07/2.13  Index Insertion      : 0.00
% 6.16/2.13  Index Deletion       : 0.00
% 6.16/2.13  Index Matching       : 0.00
% 6.16/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
