%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:57 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 137 expanded)
%              Number of leaves         :   23 (  61 expanded)
%              Depth                    :    8
%              Number of atoms          :  123 ( 463 expanded)
%              Number of equality atoms :  108 ( 406 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
       => ~ ( A != k1_xboole_0
            & B != k1_xboole_0
            & C != k1_xboole_0
            & ? [E,F,G] :
                ( D = k3_mcart_1(E,F,G)
                & ~ ( k5_mcart_1(A,B,C,D) = E
                    & k6_mcart_1(A,B,C,D) = F
                    & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_mcart_1(A,B,C) = k3_mcart_1(D,E,F)
     => ( A = D
        & B = E
        & C = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_230,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k7_mcart_1(A_75,B_76,C_77,D_78) = k2_mcart_1(D_78)
      | ~ m1_subset_1(D_78,k3_zfmisc_1(A_75,B_76,C_77))
      | k1_xboole_0 = C_77
      | k1_xboole_0 = B_76
      | k1_xboole_0 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_233,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_230])).

tff(c_236,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_233])).

tff(c_16,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7'
    | k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6'
    | k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_59,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_83,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k7_mcart_1(A_47,B_48,C_49,D_50) = k2_mcart_1(D_50)
      | ~ m1_subset_1(D_50,k3_zfmisc_1(A_47,B_48,C_49))
      | k1_xboole_0 = C_49
      | k1_xboole_0 = B_48
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_86,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_89,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_86])).

tff(c_122,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k3_mcart_1(k5_mcart_1(A_59,B_60,C_61,D_62),k6_mcart_1(A_59,B_60,C_61,D_62),k7_mcart_1(A_59,B_60,C_61,D_62)) = D_62
      | ~ m1_subset_1(D_62,k3_zfmisc_1(A_59,B_60,C_61))
      | k1_xboole_0 = C_61
      | k1_xboole_0 = B_60
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_158,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | ~ m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_122])).

tff(c_162,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_158])).

tff(c_163,plain,(
    k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_162])).

tff(c_18,plain,(
    k3_mcart_1('#skF_5','#skF_6','#skF_7') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_35,plain,(
    ! [A_25,E_21,D_22,F_20,B_23,C_24] :
      ( D_22 = A_25
      | k3_mcart_1(D_22,E_21,F_20) != k3_mcart_1(A_25,B_23,C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_25,B_23,C_24] :
      ( A_25 = '#skF_5'
      | k3_mcart_1(A_25,B_23,C_24) != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_35])).

tff(c_185,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_38])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_185])).

tff(c_200,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6'
    | k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_229,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_237,plain,(
    k2_mcart_1('#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_229])).

tff(c_201,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_270,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( k3_mcart_1(k5_mcart_1(A_87,B_88,C_89,D_90),k6_mcart_1(A_87,B_88,C_89,D_90),k7_mcart_1(A_87,B_88,C_89,D_90)) = D_90
      | ~ m1_subset_1(D_90,k3_zfmisc_1(A_87,B_88,C_89))
      | k1_xboole_0 = C_89
      | k1_xboole_0 = B_88
      | k1_xboole_0 = A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_309,plain,
    ( k3_mcart_1('#skF_5',k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_270])).

tff(c_316,plain,
    ( k3_mcart_1('#skF_5',k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_236,c_309])).

tff(c_317,plain,(
    k3_mcart_1('#skF_5',k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_316])).

tff(c_210,plain,(
    ! [B_66,F_63,C_67,D_65,A_68,E_64] :
      ( F_63 = C_67
      | k3_mcart_1(D_65,E_64,F_63) != k3_mcart_1(A_68,B_66,C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_213,plain,(
    ! [C_67,A_68,B_66] :
      ( C_67 = '#skF_7'
      | k3_mcart_1(A_68,B_66,C_67) != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_210])).

tff(c_321,plain,(
    k2_mcart_1('#skF_4') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_213])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_321])).

tff(c_352,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_353,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_397,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k3_mcart_1(k5_mcart_1(A_103,B_104,C_105,D_106),k6_mcart_1(A_103,B_104,C_105,D_106),k7_mcart_1(A_103,B_104,C_105,D_106)) = D_106
      | ~ m1_subset_1(D_106,k3_zfmisc_1(A_103,B_104,C_105))
      | k1_xboole_0 = C_105
      | k1_xboole_0 = B_104
      | k1_xboole_0 = A_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_433,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_397])).

tff(c_440,plain,
    ( k3_mcart_1('#skF_5',k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7') = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_201,c_433])).

tff(c_441,plain,(
    k3_mcart_1('#skF_5',k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_7') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_440])).

tff(c_52,plain,(
    ! [C_33,F_29,B_32,A_34,D_31,E_30] :
      ( E_30 = B_32
      | k3_mcart_1(D_31,E_30,F_29) != k3_mcart_1(A_34,B_32,C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [B_32,A_34,C_33] :
      ( B_32 = '#skF_6'
      | k3_mcart_1(A_34,B_32,C_33) != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_52])).

tff(c_451,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_55])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.36  
% 2.55/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.36  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.55/1.36  
% 2.55/1.36  %Foreground sorts:
% 2.55/1.36  
% 2.55/1.36  
% 2.55/1.36  %Background operators:
% 2.55/1.36  
% 2.55/1.36  
% 2.55/1.36  %Foreground operators:
% 2.55/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.36  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.55/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.55/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.55/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.55/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.36  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.55/1.36  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.55/1.36  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.55/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.36  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.55/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.36  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.55/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.36  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.55/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.36  
% 2.55/1.38  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_mcart_1)).
% 2.55/1.38  tff(f_69, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 2.55/1.38  tff(f_49, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 2.55/1.38  tff(f_33, axiom, (![A, B, C, D, E, F]: ((k3_mcart_1(A, B, C) = k3_mcart_1(D, E, F)) => (((A = D) & (B = E)) & (C = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_mcart_1)).
% 2.55/1.38  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.38  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.38  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.38  tff(c_26, plain, (m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.38  tff(c_230, plain, (![A_75, B_76, C_77, D_78]: (k7_mcart_1(A_75, B_76, C_77, D_78)=k2_mcart_1(D_78) | ~m1_subset_1(D_78, k3_zfmisc_1(A_75, B_76, C_77)) | k1_xboole_0=C_77 | k1_xboole_0=B_76 | k1_xboole_0=A_75)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.55/1.38  tff(c_233, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_230])).
% 2.55/1.38  tff(c_236, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_233])).
% 2.55/1.38  tff(c_16, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7' | k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6' | k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.38  tff(c_59, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_16])).
% 2.55/1.38  tff(c_83, plain, (![A_47, B_48, C_49, D_50]: (k7_mcart_1(A_47, B_48, C_49, D_50)=k2_mcart_1(D_50) | ~m1_subset_1(D_50, k3_zfmisc_1(A_47, B_48, C_49)) | k1_xboole_0=C_49 | k1_xboole_0=B_48 | k1_xboole_0=A_47)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.55/1.38  tff(c_86, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_83])).
% 2.55/1.38  tff(c_89, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_86])).
% 2.55/1.38  tff(c_122, plain, (![A_59, B_60, C_61, D_62]: (k3_mcart_1(k5_mcart_1(A_59, B_60, C_61, D_62), k6_mcart_1(A_59, B_60, C_61, D_62), k7_mcart_1(A_59, B_60, C_61, D_62))=D_62 | ~m1_subset_1(D_62, k3_zfmisc_1(A_59, B_60, C_61)) | k1_xboole_0=C_61 | k1_xboole_0=B_60 | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.38  tff(c_158, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | ~m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_89, c_122])).
% 2.55/1.38  tff(c_162, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_158])).
% 2.55/1.38  tff(c_163, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_162])).
% 2.55/1.38  tff(c_18, plain, (k3_mcart_1('#skF_5', '#skF_6', '#skF_7')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.55/1.38  tff(c_35, plain, (![A_25, E_21, D_22, F_20, B_23, C_24]: (D_22=A_25 | k3_mcart_1(D_22, E_21, F_20)!=k3_mcart_1(A_25, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.55/1.38  tff(c_38, plain, (![A_25, B_23, C_24]: (A_25='#skF_5' | k3_mcart_1(A_25, B_23, C_24)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_35])).
% 2.55/1.38  tff(c_185, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_163, c_38])).
% 2.55/1.38  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_185])).
% 2.55/1.38  tff(c_200, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6' | k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(splitRight, [status(thm)], [c_16])).
% 2.55/1.38  tff(c_229, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(splitLeft, [status(thm)], [c_200])).
% 2.55/1.38  tff(c_237, plain, (k2_mcart_1('#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_229])).
% 2.55/1.38  tff(c_201, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_16])).
% 2.55/1.38  tff(c_270, plain, (![A_87, B_88, C_89, D_90]: (k3_mcart_1(k5_mcart_1(A_87, B_88, C_89, D_90), k6_mcart_1(A_87, B_88, C_89, D_90), k7_mcart_1(A_87, B_88, C_89, D_90))=D_90 | ~m1_subset_1(D_90, k3_zfmisc_1(A_87, B_88, C_89)) | k1_xboole_0=C_89 | k1_xboole_0=B_88 | k1_xboole_0=A_87)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.38  tff(c_309, plain, (k3_mcart_1('#skF_5', k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_201, c_270])).
% 2.55/1.38  tff(c_316, plain, (k3_mcart_1('#skF_5', k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_236, c_309])).
% 2.55/1.38  tff(c_317, plain, (k3_mcart_1('#skF_5', k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_316])).
% 2.55/1.38  tff(c_210, plain, (![B_66, F_63, C_67, D_65, A_68, E_64]: (F_63=C_67 | k3_mcart_1(D_65, E_64, F_63)!=k3_mcart_1(A_68, B_66, C_67))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.55/1.38  tff(c_213, plain, (![C_67, A_68, B_66]: (C_67='#skF_7' | k3_mcart_1(A_68, B_66, C_67)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_210])).
% 2.55/1.38  tff(c_321, plain, (k2_mcart_1('#skF_4')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_317, c_213])).
% 2.55/1.38  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_321])).
% 2.55/1.38  tff(c_352, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_200])).
% 2.55/1.38  tff(c_353, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(splitRight, [status(thm)], [c_200])).
% 2.55/1.38  tff(c_397, plain, (![A_103, B_104, C_105, D_106]: (k3_mcart_1(k5_mcart_1(A_103, B_104, C_105, D_106), k6_mcart_1(A_103, B_104, C_105, D_106), k7_mcart_1(A_103, B_104, C_105, D_106))=D_106 | ~m1_subset_1(D_106, k3_zfmisc_1(A_103, B_104, C_105)) | k1_xboole_0=C_105 | k1_xboole_0=B_104 | k1_xboole_0=A_103)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.38  tff(c_433, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7')='#skF_4' | ~m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_353, c_397])).
% 2.55/1.38  tff(c_440, plain, (k3_mcart_1('#skF_5', k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7')='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_201, c_433])).
% 2.55/1.38  tff(c_441, plain, (k3_mcart_1('#skF_5', k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_7')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_440])).
% 2.55/1.38  tff(c_52, plain, (![C_33, F_29, B_32, A_34, D_31, E_30]: (E_30=B_32 | k3_mcart_1(D_31, E_30, F_29)!=k3_mcart_1(A_34, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.55/1.38  tff(c_55, plain, (![B_32, A_34, C_33]: (B_32='#skF_6' | k3_mcart_1(A_34, B_32, C_33)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_52])).
% 2.55/1.38  tff(c_451, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_441, c_55])).
% 2.55/1.38  tff(c_480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_352, c_451])).
% 2.55/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.38  
% 2.55/1.38  Inference rules
% 2.55/1.38  ----------------------
% 2.55/1.38  #Ref     : 4
% 2.55/1.38  #Sup     : 117
% 2.55/1.38  #Fact    : 0
% 2.55/1.38  #Define  : 0
% 2.55/1.38  #Split   : 2
% 2.55/1.38  #Chain   : 0
% 2.55/1.38  #Close   : 0
% 2.55/1.38  
% 2.55/1.38  Ordering : KBO
% 2.55/1.38  
% 2.55/1.38  Simplification rules
% 2.55/1.38  ----------------------
% 2.55/1.38  #Subsume      : 5
% 2.55/1.38  #Demod        : 13
% 2.55/1.38  #Tautology    : 43
% 2.55/1.38  #SimpNegUnit  : 17
% 2.55/1.38  #BackRed      : 1
% 2.55/1.38  
% 2.55/1.38  #Partial instantiations: 0
% 2.55/1.38  #Strategies tried      : 1
% 2.55/1.38  
% 2.55/1.38  Timing (in seconds)
% 2.55/1.38  ----------------------
% 2.65/1.38  Preprocessing        : 0.29
% 2.65/1.38  Parsing              : 0.15
% 2.65/1.38  CNF conversion       : 0.02
% 2.65/1.38  Main loop            : 0.27
% 2.65/1.38  Inferencing          : 0.11
% 2.65/1.38  Reduction            : 0.07
% 2.65/1.38  Demodulation         : 0.04
% 2.65/1.38  BG Simplification    : 0.02
% 2.65/1.38  Subsumption          : 0.06
% 2.65/1.38  Abstraction          : 0.01
% 2.65/1.38  MUC search           : 0.00
% 2.65/1.38  Cooper               : 0.00
% 2.65/1.38  Total                : 0.59
% 2.65/1.38  Index Insertion      : 0.00
% 2.65/1.38  Index Deletion       : 0.00
% 2.65/1.38  Index Matching       : 0.00
% 2.65/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
