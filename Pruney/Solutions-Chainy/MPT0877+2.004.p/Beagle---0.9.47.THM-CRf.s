%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:29 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 664 expanded)
%              Number of leaves         :   14 ( 187 expanded)
%              Depth                    :   13
%              Number of atoms          :  182 (2028 expanded)
%              Number of equality atoms :  172 (2018 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
       => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
          | ( A = D
            & B = E
            & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_16,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_67,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_20,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    ! [A_24,C_21,D_22,F_20,B_19,E_23] :
      ( D_22 = A_24
      | k1_xboole_0 = C_21
      | k1_xboole_0 = B_19
      | k1_xboole_0 = A_24
      | k3_zfmisc_1(D_22,E_23,F_20) != k3_zfmisc_1(A_24,B_19,C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,(
    ! [A_24,C_21,B_19] :
      ( A_24 = '#skF_1'
      | k1_xboole_0 = C_21
      | k1_xboole_0 = B_19
      | k1_xboole_0 = A_24
      | k3_zfmisc_1(A_24,B_19,C_21) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_95])).

tff(c_125,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_98])).

tff(c_126,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_125])).

tff(c_142,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_8,plain,(
    ! [B_2,C_3] : k3_zfmisc_1(k1_xboole_0,B_2,C_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_146,plain,(
    ! [B_2,C_3] : k3_zfmisc_1('#skF_4',B_2,C_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_142,c_8])).

tff(c_18,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_21,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18])).

tff(c_149,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_21])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_149])).

tff(c_240,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_316,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_4,plain,(
    ! [A_1,B_2] : k3_zfmisc_1(A_1,B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_323,plain,(
    ! [A_1,B_2] : k3_zfmisc_1(A_1,B_2,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_316,c_4])).

tff(c_325,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_21])).

tff(c_391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_325])).

tff(c_392,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_6,plain,(
    ! [A_1,C_3] : k3_zfmisc_1(A_1,k1_xboole_0,C_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_402,plain,(
    ! [A_1,C_3] : k3_zfmisc_1(A_1,'#skF_5',C_3) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_392,c_6])).

tff(c_403,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_21])).

tff(c_480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_403])).

tff(c_481,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_487,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_481])).

tff(c_482,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_488,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_20])).

tff(c_517,plain,(
    ! [D_77,F_75,B_74,C_76,A_79,E_78] :
      ( D_77 = A_79
      | k1_xboole_0 = C_76
      | k1_xboole_0 = B_74
      | k1_xboole_0 = A_79
      | k3_zfmisc_1(D_77,E_78,F_75) != k3_zfmisc_1(A_79,B_74,C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_523,plain,(
    ! [D_77,E_78,F_75] :
      ( D_77 = '#skF_4'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1(D_77,E_78,F_75) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_517])).

tff(c_545,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_523])).

tff(c_549,plain,(
    ! [B_2,C_3] : k3_zfmisc_1('#skF_4',B_2,C_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_545,c_8])).

tff(c_489,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_21])).

tff(c_548,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_489])).

tff(c_581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_548])).

tff(c_583,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_523])).

tff(c_582,plain,(
    ! [D_77,E_78,F_75] :
      ( k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_6'
      | D_77 = '#skF_4'
      | k3_zfmisc_1(D_77,E_78,F_75) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_523])).

tff(c_616,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_582])).

tff(c_621,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_489])).

tff(c_623,plain,(
    ! [A_1,B_2] : k3_zfmisc_1(A_1,B_2,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_616,c_4])).

tff(c_668,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_488])).

tff(c_670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_621,c_668])).

tff(c_671,plain,(
    ! [D_77,E_78,F_75] :
      ( k1_xboole_0 = '#skF_5'
      | D_77 = '#skF_4'
      | k3_zfmisc_1(D_77,E_78,F_75) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_582])).

tff(c_706,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_671])).

tff(c_713,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_489])).

tff(c_716,plain,(
    ! [A_1,C_3] : k3_zfmisc_1(A_1,'#skF_5',C_3) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_706,c_6])).

tff(c_732,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_488])).

tff(c_791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_732])).

tff(c_793,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_671])).

tff(c_672,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_582])).

tff(c_588,plain,(
    ! [E_88,F_85,C_86,B_84,A_89,D_87] :
      ( E_88 = B_84
      | k1_xboole_0 = C_86
      | k1_xboole_0 = B_84
      | k1_xboole_0 = A_89
      | k3_zfmisc_1(D_87,E_88,F_85) != k3_zfmisc_1(A_89,B_84,C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_594,plain,(
    ! [E_88,D_87,F_85] :
      ( E_88 = '#skF_5'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1(D_87,E_88,F_85) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_588])).

tff(c_813,plain,(
    ! [E_88,D_87,F_85] :
      ( E_88 = '#skF_5'
      | k3_zfmisc_1(D_87,E_88,F_85) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_793,c_672,c_594])).

tff(c_816,plain,(
    '#skF_5' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_813])).

tff(c_834,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_793])).

tff(c_677,plain,(
    ! [C_99,A_102,D_100,B_97,E_101,F_98] :
      ( F_98 = C_99
      | k1_xboole_0 = C_99
      | k1_xboole_0 = B_97
      | k1_xboole_0 = A_102
      | k3_zfmisc_1(D_100,E_101,F_98) != k3_zfmisc_1(A_102,B_97,C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_683,plain,(
    ! [F_98,D_100,E_101] :
      ( F_98 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1(D_100,E_101,F_98) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_677])).

tff(c_702,plain,(
    ! [F_98,D_100,E_101] :
      ( F_98 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k3_zfmisc_1(D_100,E_101,F_98) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_683])).

tff(c_892,plain,(
    ! [F_98,D_100,E_101] :
      ( F_98 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_2'
      | k3_zfmisc_1(D_100,E_101,F_98) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_702])).

tff(c_893,plain,(
    ! [F_98,D_100,E_101] :
      ( F_98 = '#skF_6'
      | k3_zfmisc_1(D_100,E_101,F_98) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_834,c_672,c_892])).

tff(c_896,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_893])).

tff(c_898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_896])).

tff(c_899,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_481])).

tff(c_900,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_481])).

tff(c_906,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_482,c_20])).

tff(c_967,plain,(
    ! [C_132,D_133,F_131,E_134,B_130,A_135] :
      ( E_134 = B_130
      | k1_xboole_0 = C_132
      | k1_xboole_0 = B_130
      | k1_xboole_0 = A_135
      | k3_zfmisc_1(D_133,E_134,F_131) != k3_zfmisc_1(A_135,B_130,C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_973,plain,(
    ! [E_134,D_133,F_131] :
      ( E_134 = '#skF_5'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1(D_133,E_134,F_131) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_967])).

tff(c_1027,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_973])).

tff(c_1033,plain,(
    ! [B_2,C_3] : k3_zfmisc_1('#skF_4',B_2,C_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_1027,c_8])).

tff(c_901,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_21])).

tff(c_907,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_901])).

tff(c_1032,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_907])).

tff(c_1051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1033,c_1032])).

tff(c_1053,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_973])).

tff(c_1052,plain,(
    ! [E_134,D_133,F_131] :
      ( k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_3'
      | E_134 = '#skF_5'
      | k3_zfmisc_1(D_133,E_134,F_131) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_973])).

tff(c_1054,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1052])).

tff(c_1062,plain,(
    ! [A_1,B_2] : k3_zfmisc_1(A_1,B_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_1054,c_4])).

tff(c_1060,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_907])).

tff(c_1078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1062,c_1060])).

tff(c_1080,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1052])).

tff(c_970,plain,(
    ! [B_130,C_132,A_135] :
      ( B_130 = '#skF_5'
      | k1_xboole_0 = C_132
      | k1_xboole_0 = B_130
      | k1_xboole_0 = A_135
      | k3_zfmisc_1(A_135,B_130,C_132) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_967])).

tff(c_1145,plain,
    ( '#skF_5' = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_970])).

tff(c_1146,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1053,c_1080,c_899,c_1145])).

tff(c_1079,plain,(
    ! [E_134,D_133,F_131] :
      ( k1_xboole_0 = '#skF_5'
      | E_134 = '#skF_5'
      | k3_zfmisc_1(D_133,E_134,F_131) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1052])).

tff(c_1192,plain,(
    ! [E_134,D_133,F_131] :
      ( '#skF_5' = '#skF_2'
      | E_134 = '#skF_5'
      | k3_zfmisc_1(D_133,E_134,F_131) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_1079])).

tff(c_1193,plain,(
    ! [E_134,D_133,F_131] :
      ( E_134 = '#skF_5'
      | k3_zfmisc_1(D_133,E_134,F_131) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_899,c_1192])).

tff(c_1196,plain,(
    '#skF_5' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1193])).

tff(c_1198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_899,c_1196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.45  %$ k3_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.86/1.45  
% 2.86/1.45  %Foreground sorts:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Background operators:
% 2.86/1.45  
% 2.86/1.45  
% 2.86/1.45  %Foreground operators:
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.86/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.45  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.45  
% 3.18/1.47  tff(f_62, negated_conjecture, ~(![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 3.18/1.47  tff(f_51, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_mcart_1)).
% 3.18/1.47  tff(f_37, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 3.18/1.47  tff(c_16, plain, ('#skF_6'!='#skF_3' | '#skF_5'!='#skF_2' | '#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.47  tff(c_67, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_16])).
% 3.18/1.47  tff(c_20, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.47  tff(c_95, plain, (![A_24, C_21, D_22, F_20, B_19, E_23]: (D_22=A_24 | k1_xboole_0=C_21 | k1_xboole_0=B_19 | k1_xboole_0=A_24 | k3_zfmisc_1(D_22, E_23, F_20)!=k3_zfmisc_1(A_24, B_19, C_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.47  tff(c_98, plain, (![A_24, C_21, B_19]: (A_24='#skF_1' | k1_xboole_0=C_21 | k1_xboole_0=B_19 | k1_xboole_0=A_24 | k3_zfmisc_1(A_24, B_19, C_21)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_95])).
% 3.18/1.47  tff(c_125, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_98])).
% 3.18/1.47  tff(c_126, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_67, c_125])).
% 3.18/1.47  tff(c_142, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_126])).
% 3.18/1.47  tff(c_8, plain, (![B_2, C_3]: (k3_zfmisc_1(k1_xboole_0, B_2, C_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.47  tff(c_146, plain, (![B_2, C_3]: (k3_zfmisc_1('#skF_4', B_2, C_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_142, c_8])).
% 3.18/1.47  tff(c_18, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.47  tff(c_21, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18])).
% 3.18/1.47  tff(c_149, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_21])).
% 3.18/1.47  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_149])).
% 3.18/1.47  tff(c_240, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_126])).
% 3.18/1.47  tff(c_316, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_240])).
% 3.18/1.47  tff(c_4, plain, (![A_1, B_2]: (k3_zfmisc_1(A_1, B_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.47  tff(c_323, plain, (![A_1, B_2]: (k3_zfmisc_1(A_1, B_2, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_316, c_4])).
% 3.18/1.47  tff(c_325, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_316, c_21])).
% 3.18/1.47  tff(c_391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_323, c_325])).
% 3.18/1.47  tff(c_392, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_240])).
% 3.18/1.47  tff(c_6, plain, (![A_1, C_3]: (k3_zfmisc_1(A_1, k1_xboole_0, C_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.47  tff(c_402, plain, (![A_1, C_3]: (k3_zfmisc_1(A_1, '#skF_5', C_3)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_392, c_392, c_6])).
% 3.18/1.47  tff(c_403, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_392, c_21])).
% 3.18/1.47  tff(c_480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_402, c_403])).
% 3.18/1.47  tff(c_481, plain, ('#skF_5'!='#skF_2' | '#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_16])).
% 3.18/1.47  tff(c_487, plain, ('#skF_6'!='#skF_3'), inference(splitLeft, [status(thm)], [c_481])).
% 3.18/1.47  tff(c_482, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_16])).
% 3.18/1.47  tff(c_488, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_482, c_20])).
% 3.18/1.47  tff(c_517, plain, (![D_77, F_75, B_74, C_76, A_79, E_78]: (D_77=A_79 | k1_xboole_0=C_76 | k1_xboole_0=B_74 | k1_xboole_0=A_79 | k3_zfmisc_1(D_77, E_78, F_75)!=k3_zfmisc_1(A_79, B_74, C_76))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.47  tff(c_523, plain, (![D_77, E_78, F_75]: (D_77='#skF_4' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k3_zfmisc_1(D_77, E_78, F_75)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_488, c_517])).
% 3.18/1.47  tff(c_545, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_523])).
% 3.18/1.47  tff(c_549, plain, (![B_2, C_3]: (k3_zfmisc_1('#skF_4', B_2, C_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_545, c_545, c_8])).
% 3.18/1.47  tff(c_489, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_488, c_21])).
% 3.18/1.47  tff(c_548, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_545, c_489])).
% 3.18/1.47  tff(c_581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_549, c_548])).
% 3.18/1.47  tff(c_583, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_523])).
% 3.18/1.47  tff(c_582, plain, (![D_77, E_78, F_75]: (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | D_77='#skF_4' | k3_zfmisc_1(D_77, E_78, F_75)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_523])).
% 3.18/1.47  tff(c_616, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_582])).
% 3.18/1.47  tff(c_621, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_616, c_489])).
% 3.18/1.47  tff(c_623, plain, (![A_1, B_2]: (k3_zfmisc_1(A_1, B_2, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_616, c_4])).
% 3.18/1.47  tff(c_668, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_623, c_488])).
% 3.18/1.47  tff(c_670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_621, c_668])).
% 3.18/1.47  tff(c_671, plain, (![D_77, E_78, F_75]: (k1_xboole_0='#skF_5' | D_77='#skF_4' | k3_zfmisc_1(D_77, E_78, F_75)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_582])).
% 3.18/1.47  tff(c_706, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_671])).
% 3.18/1.47  tff(c_713, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_706, c_489])).
% 3.18/1.47  tff(c_716, plain, (![A_1, C_3]: (k3_zfmisc_1(A_1, '#skF_5', C_3)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_706, c_706, c_6])).
% 3.18/1.47  tff(c_732, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_716, c_488])).
% 3.18/1.47  tff(c_791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_713, c_732])).
% 3.18/1.47  tff(c_793, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_671])).
% 3.18/1.47  tff(c_672, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_582])).
% 3.18/1.47  tff(c_588, plain, (![E_88, F_85, C_86, B_84, A_89, D_87]: (E_88=B_84 | k1_xboole_0=C_86 | k1_xboole_0=B_84 | k1_xboole_0=A_89 | k3_zfmisc_1(D_87, E_88, F_85)!=k3_zfmisc_1(A_89, B_84, C_86))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.47  tff(c_594, plain, (![E_88, D_87, F_85]: (E_88='#skF_5' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k3_zfmisc_1(D_87, E_88, F_85)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_488, c_588])).
% 3.18/1.47  tff(c_813, plain, (![E_88, D_87, F_85]: (E_88='#skF_5' | k3_zfmisc_1(D_87, E_88, F_85)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_583, c_793, c_672, c_594])).
% 3.18/1.47  tff(c_816, plain, ('#skF_5'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_813])).
% 3.18/1.47  tff(c_834, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_816, c_793])).
% 3.18/1.47  tff(c_677, plain, (![C_99, A_102, D_100, B_97, E_101, F_98]: (F_98=C_99 | k1_xboole_0=C_99 | k1_xboole_0=B_97 | k1_xboole_0=A_102 | k3_zfmisc_1(D_100, E_101, F_98)!=k3_zfmisc_1(A_102, B_97, C_99))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.47  tff(c_683, plain, (![F_98, D_100, E_101]: (F_98='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k3_zfmisc_1(D_100, E_101, F_98)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_488, c_677])).
% 3.18/1.47  tff(c_702, plain, (![F_98, D_100, E_101]: (F_98='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k3_zfmisc_1(D_100, E_101, F_98)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_583, c_683])).
% 3.18/1.47  tff(c_892, plain, (![F_98, D_100, E_101]: (F_98='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_2' | k3_zfmisc_1(D_100, E_101, F_98)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_816, c_702])).
% 3.18/1.47  tff(c_893, plain, (![F_98, D_100, E_101]: (F_98='#skF_6' | k3_zfmisc_1(D_100, E_101, F_98)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_834, c_672, c_892])).
% 3.18/1.47  tff(c_896, plain, ('#skF_6'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_893])).
% 3.18/1.47  tff(c_898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_487, c_896])).
% 3.18/1.47  tff(c_899, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_481])).
% 3.18/1.47  tff(c_900, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_481])).
% 3.18/1.47  tff(c_906, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_900, c_482, c_20])).
% 3.18/1.47  tff(c_967, plain, (![C_132, D_133, F_131, E_134, B_130, A_135]: (E_134=B_130 | k1_xboole_0=C_132 | k1_xboole_0=B_130 | k1_xboole_0=A_135 | k3_zfmisc_1(D_133, E_134, F_131)!=k3_zfmisc_1(A_135, B_130, C_132))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.47  tff(c_973, plain, (![E_134, D_133, F_131]: (E_134='#skF_5' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k3_zfmisc_1(D_133, E_134, F_131)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_906, c_967])).
% 3.18/1.47  tff(c_1027, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_973])).
% 3.18/1.47  tff(c_1033, plain, (![B_2, C_3]: (k3_zfmisc_1('#skF_4', B_2, C_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_1027, c_8])).
% 3.18/1.47  tff(c_901, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_900, c_21])).
% 3.18/1.47  tff(c_907, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_906, c_901])).
% 3.18/1.47  tff(c_1032, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1027, c_907])).
% 3.18/1.47  tff(c_1051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1033, c_1032])).
% 3.18/1.47  tff(c_1053, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_973])).
% 3.18/1.47  tff(c_1052, plain, (![E_134, D_133, F_131]: (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_3' | E_134='#skF_5' | k3_zfmisc_1(D_133, E_134, F_131)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_973])).
% 3.18/1.47  tff(c_1054, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1052])).
% 3.18/1.47  tff(c_1062, plain, (![A_1, B_2]: (k3_zfmisc_1(A_1, B_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_1054, c_4])).
% 3.18/1.47  tff(c_1060, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1054, c_907])).
% 3.18/1.47  tff(c_1078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1062, c_1060])).
% 3.18/1.47  tff(c_1080, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1052])).
% 3.18/1.47  tff(c_970, plain, (![B_130, C_132, A_135]: (B_130='#skF_5' | k1_xboole_0=C_132 | k1_xboole_0=B_130 | k1_xboole_0=A_135 | k3_zfmisc_1(A_135, B_130, C_132)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_906, c_967])).
% 3.18/1.47  tff(c_1145, plain, ('#skF_5'='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_970])).
% 3.18/1.47  tff(c_1146, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1053, c_1080, c_899, c_1145])).
% 3.18/1.47  tff(c_1079, plain, (![E_134, D_133, F_131]: (k1_xboole_0='#skF_5' | E_134='#skF_5' | k3_zfmisc_1(D_133, E_134, F_131)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1052])).
% 3.18/1.47  tff(c_1192, plain, (![E_134, D_133, F_131]: ('#skF_5'='#skF_2' | E_134='#skF_5' | k3_zfmisc_1(D_133, E_134, F_131)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1146, c_1079])).
% 3.18/1.47  tff(c_1193, plain, (![E_134, D_133, F_131]: (E_134='#skF_5' | k3_zfmisc_1(D_133, E_134, F_131)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_899, c_1192])).
% 3.18/1.47  tff(c_1196, plain, ('#skF_5'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_1193])).
% 3.18/1.47  tff(c_1198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_899, c_1196])).
% 3.18/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.47  
% 3.18/1.47  Inference rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Ref     : 22
% 3.18/1.47  #Sup     : 259
% 3.18/1.47  #Fact    : 0
% 3.18/1.47  #Define  : 0
% 3.18/1.47  #Split   : 12
% 3.18/1.47  #Chain   : 0
% 3.18/1.47  #Close   : 0
% 3.18/1.47  
% 3.18/1.47  Ordering : KBO
% 3.18/1.47  
% 3.18/1.47  Simplification rules
% 3.18/1.47  ----------------------
% 3.18/1.47  #Subsume      : 61
% 3.18/1.47  #Demod        : 278
% 3.18/1.47  #Tautology    : 188
% 3.18/1.47  #SimpNegUnit  : 31
% 3.18/1.47  #BackRed      : 117
% 3.18/1.47  
% 3.18/1.47  #Partial instantiations: 0
% 3.18/1.47  #Strategies tried      : 1
% 3.18/1.47  
% 3.18/1.47  Timing (in seconds)
% 3.18/1.47  ----------------------
% 3.18/1.47  Preprocessing        : 0.28
% 3.18/1.47  Parsing              : 0.15
% 3.18/1.47  CNF conversion       : 0.02
% 3.18/1.47  Main loop            : 0.40
% 3.18/1.47  Inferencing          : 0.12
% 3.18/1.47  Reduction            : 0.11
% 3.18/1.47  Demodulation         : 0.08
% 3.18/1.47  BG Simplification    : 0.02
% 3.18/1.47  Subsumption          : 0.11
% 3.18/1.47  Abstraction          : 0.02
% 3.18/1.47  MUC search           : 0.00
% 3.18/1.47  Cooper               : 0.00
% 3.18/1.47  Total                : 0.72
% 3.18/1.47  Index Insertion      : 0.00
% 3.18/1.47  Index Deletion       : 0.00
% 3.18/1.47  Index Matching       : 0.00
% 3.18/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
