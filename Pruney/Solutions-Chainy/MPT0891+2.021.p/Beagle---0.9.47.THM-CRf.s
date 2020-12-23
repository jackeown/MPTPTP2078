%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:43 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 181 expanded)
%              Number of leaves         :   36 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 454 expanded)
%              Number of equality atoms :  110 ( 296 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_83,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_22,plain,(
    ! [D_12,A_7] : r2_hidden(D_12,k2_tarski(A_7,D_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_5'(A_29),A_29)
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_109,plain,(
    ! [D_66,A_67,B_68] :
      ( r2_hidden(D_66,A_67)
      | ~ r2_hidden(D_66,k4_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_67,B_68)),A_67)
      | k4_xboole_0(A_67,B_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_109])).

tff(c_115,plain,(
    ! [D_69,B_70,A_71] :
      ( ~ r2_hidden(D_69,B_70)
      | ~ r2_hidden(D_69,k4_xboole_0(A_71,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1408,plain,(
    ! [A_301,B_302] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_301,B_302)),B_302)
      | k4_xboole_0(A_301,B_302) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_1413,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_114,c_1408])).

tff(c_2589,plain,(
    ! [B_499,C_500,A_501] :
      ( ~ r2_hidden(B_499,C_500)
      | k4_xboole_0(k2_tarski(A_501,B_499),C_500) != k2_tarski(A_501,B_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2593,plain,(
    ! [B_499,A_501] :
      ( ~ r2_hidden(B_499,k2_tarski(A_501,B_499))
      | k2_tarski(A_501,B_499) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1413,c_2589])).

tff(c_2595,plain,(
    ! [A_501,B_499] : k2_tarski(A_501,B_499) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2593])).

tff(c_136,plain,(
    ! [D_75,B_76,A_77] :
      ( D_75 = B_76
      | D_75 = A_77
      | ~ r2_hidden(D_75,k2_tarski(A_77,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_147,plain,(
    ! [A_77,B_76] :
      ( '#skF_5'(k2_tarski(A_77,B_76)) = B_76
      | '#skF_5'(k2_tarski(A_77,B_76)) = A_77
      | k2_tarski(A_77,B_76) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_136])).

tff(c_2822,plain,(
    ! [A_77,B_76] :
      ( '#skF_5'(k2_tarski(A_77,B_76)) = B_76
      | '#skF_5'(k2_tarski(A_77,B_76)) = A_77 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2595,c_147])).

tff(c_2950,plain,(
    ! [B_583] : '#skF_5'(k2_tarski(B_583,B_583)) = B_583 ),
    inference(factorization,[status(thm),theory(equality)],[c_2822])).

tff(c_24,plain,(
    ! [D_12,B_8] : r2_hidden(D_12,k2_tarski(D_12,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2623,plain,(
    ! [D_510,A_511,C_512,E_513] :
      ( ~ r2_hidden(D_510,A_511)
      | k3_mcart_1(C_512,D_510,E_513) != '#skF_5'(A_511)
      | k1_xboole_0 = A_511 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2631,plain,(
    ! [C_512,D_12,E_513,B_8] :
      ( k3_mcart_1(C_512,D_12,E_513) != '#skF_5'(k2_tarski(D_12,B_8))
      | k2_tarski(D_12,B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_2623])).

tff(c_2639,plain,(
    ! [C_512,D_12,E_513,B_8] : k3_mcart_1(C_512,D_12,E_513) != '#skF_5'(k2_tarski(D_12,B_8)) ),
    inference(negUnitSimplification,[status(thm)],[c_2595,c_2631])).

tff(c_2991,plain,(
    ! [C_512,B_583,E_513] : k3_mcart_1(C_512,B_583,E_513) != B_583 ),
    inference(superposition,[status(thm),theory(equality)],[c_2950,c_2639])).

tff(c_68,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_152,plain,(
    ! [A_78,B_79,C_80] : k4_tarski(k4_tarski(A_78,B_79),C_80) = k3_mcart_1(A_78,B_79,C_80) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    ! [A_48,B_49] : k2_mcart_1(k4_tarski(A_48,B_49)) = B_49 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    ! [B_27,C_28] : k2_mcart_1(k4_tarski(B_27,C_28)) != k4_tarski(B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_76,plain,(
    ! [B_27,C_28] : k4_tarski(B_27,C_28) != C_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_50])).

tff(c_167,plain,(
    ! [A_78,B_79,C_80] : k3_mcart_1(A_78,B_79,C_80) != C_80 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_76])).

tff(c_220,plain,(
    ! [A_95,B_96] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_95,B_96)),B_96)
      | k4_xboole_0(A_95,B_96) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_54,c_115])).

tff(c_225,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_114,c_220])).

tff(c_285,plain,(
    ! [A_105,C_106,B_107] :
      ( ~ r2_hidden(A_105,C_106)
      | k4_xboole_0(k2_tarski(A_105,B_107),C_106) != k2_tarski(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_289,plain,(
    ! [A_105,B_107] :
      ( ~ r2_hidden(A_105,k2_tarski(A_105,B_107))
      | k2_tarski(A_105,B_107) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_285])).

tff(c_291,plain,(
    ! [A_105,B_107] : k2_tarski(A_105,B_107) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_289])).

tff(c_549,plain,(
    ! [A_77,B_76] :
      ( '#skF_5'(k2_tarski(A_77,B_76)) = B_76
      | '#skF_5'(k2_tarski(A_77,B_76)) = A_77 ) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_147])).

tff(c_708,plain,(
    ! [B_193] : '#skF_5'(k2_tarski(B_193,B_193)) = B_193 ),
    inference(factorization,[status(thm),theory(equality)],[c_549])).

tff(c_226,plain,(
    ! [C_97,A_98,D_99,E_100] :
      ( ~ r2_hidden(C_97,A_98)
      | k3_mcart_1(C_97,D_99,E_100) != '#skF_5'(A_98)
      | k1_xboole_0 = A_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_237,plain,(
    ! [D_12,D_99,E_100,B_8] :
      ( k3_mcart_1(D_12,D_99,E_100) != '#skF_5'(k2_tarski(D_12,B_8))
      | k2_tarski(D_12,B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_226])).

tff(c_503,plain,(
    ! [D_12,D_99,E_100,B_8] : k3_mcart_1(D_12,D_99,E_100) != '#skF_5'(k2_tarski(D_12,B_8)) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_237])).

tff(c_728,plain,(
    ! [B_193,D_99,E_100] : k3_mcart_1(B_193,D_99,E_100) != B_193 ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_503])).

tff(c_66,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_189,plain,(
    k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1300,plain,(
    ! [A_289,B_290,C_291,D_292] :
      ( k3_mcart_1(k5_mcart_1(A_289,B_290,C_291,D_292),k6_mcart_1(A_289,B_290,C_291,D_292),k7_mcart_1(A_289,B_290,C_291,D_292)) = D_292
      | ~ m1_subset_1(D_292,k3_zfmisc_1(A_289,B_290,C_291))
      | k1_xboole_0 = C_291
      | k1_xboole_0 = B_290
      | k1_xboole_0 = A_289 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1369,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_1300])).

tff(c_1377,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1369])).

tff(c_1379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_70,c_728,c_1377])).

tff(c_1380,plain,
    ( k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1473,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1380])).

tff(c_2472,plain,(
    ! [A_494,B_495,C_496,D_497] :
      ( k3_mcart_1(k5_mcart_1(A_494,B_495,C_496,D_497),k6_mcart_1(A_494,B_495,C_496,D_497),k7_mcart_1(A_494,B_495,C_496,D_497)) = D_497
      | ~ m1_subset_1(D_497,k3_zfmisc_1(A_494,B_495,C_496))
      | k1_xboole_0 = C_496
      | k1_xboole_0 = B_495
      | k1_xboole_0 = A_494 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2541,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1473,c_2472])).

tff(c_2549,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2541])).

tff(c_2551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_70,c_167,c_2549])).

tff(c_2552,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1380])).

tff(c_3683,plain,(
    ! [A_691,B_692,C_693,D_694] :
      ( k3_mcart_1(k5_mcart_1(A_691,B_692,C_693,D_694),k6_mcart_1(A_691,B_692,C_693,D_694),k7_mcart_1(A_691,B_692,C_693,D_694)) = D_694
      | ~ m1_subset_1(D_694,k3_zfmisc_1(A_691,B_692,C_693))
      | k1_xboole_0 = C_693
      | k1_xboole_0 = B_692
      | k1_xboole_0 = A_691 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3752,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2552,c_3683])).

tff(c_3760,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3752])).

tff(c_3762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_70,c_2991,c_3760])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:31:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.97  
% 4.85/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.97  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 4.85/1.97  
% 4.85/1.97  %Foreground sorts:
% 4.85/1.97  
% 4.85/1.97  
% 4.85/1.97  %Background operators:
% 4.85/1.97  
% 4.85/1.97  
% 4.85/1.97  %Foreground operators:
% 4.85/1.97  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.85/1.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.85/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.85/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.85/1.97  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.85/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.85/1.97  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.85/1.97  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.85/1.97  tff('#skF_7', type, '#skF_7': $i).
% 4.85/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.85/1.97  tff('#skF_6', type, '#skF_6': $i).
% 4.85/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.85/1.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.85/1.97  tff('#skF_9', type, '#skF_9': $i).
% 4.85/1.97  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.85/1.97  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.85/1.97  tff('#skF_8', type, '#skF_8': $i).
% 4.85/1.97  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.85/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/1.97  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.85/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.85/1.97  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.85/1.97  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.85/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/1.97  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.85/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.85/1.97  
% 4.85/1.98  tff(f_127, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 4.85/1.98  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.85/1.98  tff(f_83, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 4.85/1.98  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.85/1.98  tff(f_54, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 4.85/1.98  tff(f_56, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 4.85/1.98  tff(f_103, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 4.85/1.98  tff(f_67, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 4.85/1.98  tff(f_99, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 4.85/1.98  tff(c_74, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.85/1.98  tff(c_72, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.85/1.98  tff(c_70, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.85/1.98  tff(c_22, plain, (![D_12, A_7]: (r2_hidden(D_12, k2_tarski(A_7, D_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.85/1.98  tff(c_54, plain, (![A_29]: (r2_hidden('#skF_5'(A_29), A_29) | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.85/1.98  tff(c_109, plain, (![D_66, A_67, B_68]: (r2_hidden(D_66, A_67) | ~r2_hidden(D_66, k4_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.85/1.98  tff(c_114, plain, (![A_67, B_68]: (r2_hidden('#skF_5'(k4_xboole_0(A_67, B_68)), A_67) | k4_xboole_0(A_67, B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_109])).
% 4.85/1.98  tff(c_115, plain, (![D_69, B_70, A_71]: (~r2_hidden(D_69, B_70) | ~r2_hidden(D_69, k4_xboole_0(A_71, B_70)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.85/1.98  tff(c_1408, plain, (![A_301, B_302]: (~r2_hidden('#skF_5'(k4_xboole_0(A_301, B_302)), B_302) | k4_xboole_0(A_301, B_302)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_115])).
% 4.85/1.98  tff(c_1413, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_114, c_1408])).
% 4.85/1.98  tff(c_2589, plain, (![B_499, C_500, A_501]: (~r2_hidden(B_499, C_500) | k4_xboole_0(k2_tarski(A_501, B_499), C_500)!=k2_tarski(A_501, B_499))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.85/1.98  tff(c_2593, plain, (![B_499, A_501]: (~r2_hidden(B_499, k2_tarski(A_501, B_499)) | k2_tarski(A_501, B_499)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1413, c_2589])).
% 4.85/1.98  tff(c_2595, plain, (![A_501, B_499]: (k2_tarski(A_501, B_499)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2593])).
% 4.85/1.98  tff(c_136, plain, (![D_75, B_76, A_77]: (D_75=B_76 | D_75=A_77 | ~r2_hidden(D_75, k2_tarski(A_77, B_76)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.85/1.98  tff(c_147, plain, (![A_77, B_76]: ('#skF_5'(k2_tarski(A_77, B_76))=B_76 | '#skF_5'(k2_tarski(A_77, B_76))=A_77 | k2_tarski(A_77, B_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_136])).
% 4.85/1.98  tff(c_2822, plain, (![A_77, B_76]: ('#skF_5'(k2_tarski(A_77, B_76))=B_76 | '#skF_5'(k2_tarski(A_77, B_76))=A_77)), inference(negUnitSimplification, [status(thm)], [c_2595, c_147])).
% 4.85/1.98  tff(c_2950, plain, (![B_583]: ('#skF_5'(k2_tarski(B_583, B_583))=B_583)), inference(factorization, [status(thm), theory('equality')], [c_2822])).
% 4.85/1.98  tff(c_24, plain, (![D_12, B_8]: (r2_hidden(D_12, k2_tarski(D_12, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.85/1.98  tff(c_2623, plain, (![D_510, A_511, C_512, E_513]: (~r2_hidden(D_510, A_511) | k3_mcart_1(C_512, D_510, E_513)!='#skF_5'(A_511) | k1_xboole_0=A_511)), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.85/1.98  tff(c_2631, plain, (![C_512, D_12, E_513, B_8]: (k3_mcart_1(C_512, D_12, E_513)!='#skF_5'(k2_tarski(D_12, B_8)) | k2_tarski(D_12, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_2623])).
% 4.85/1.98  tff(c_2639, plain, (![C_512, D_12, E_513, B_8]: (k3_mcart_1(C_512, D_12, E_513)!='#skF_5'(k2_tarski(D_12, B_8)))), inference(negUnitSimplification, [status(thm)], [c_2595, c_2631])).
% 4.85/1.98  tff(c_2991, plain, (![C_512, B_583, E_513]: (k3_mcart_1(C_512, B_583, E_513)!=B_583)), inference(superposition, [status(thm), theory('equality')], [c_2950, c_2639])).
% 4.85/1.98  tff(c_68, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.85/1.98  tff(c_152, plain, (![A_78, B_79, C_80]: (k4_tarski(k4_tarski(A_78, B_79), C_80)=k3_mcart_1(A_78, B_79, C_80))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.85/1.98  tff(c_64, plain, (![A_48, B_49]: (k2_mcart_1(k4_tarski(A_48, B_49))=B_49)), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.85/1.98  tff(c_50, plain, (![B_27, C_28]: (k2_mcart_1(k4_tarski(B_27, C_28))!=k4_tarski(B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.85/1.98  tff(c_76, plain, (![B_27, C_28]: (k4_tarski(B_27, C_28)!=C_28)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_50])).
% 4.85/1.98  tff(c_167, plain, (![A_78, B_79, C_80]: (k3_mcart_1(A_78, B_79, C_80)!=C_80)), inference(superposition, [status(thm), theory('equality')], [c_152, c_76])).
% 4.85/1.98  tff(c_220, plain, (![A_95, B_96]: (~r2_hidden('#skF_5'(k4_xboole_0(A_95, B_96)), B_96) | k4_xboole_0(A_95, B_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_115])).
% 4.85/1.98  tff(c_225, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_114, c_220])).
% 4.85/1.98  tff(c_285, plain, (![A_105, C_106, B_107]: (~r2_hidden(A_105, C_106) | k4_xboole_0(k2_tarski(A_105, B_107), C_106)!=k2_tarski(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.85/1.98  tff(c_289, plain, (![A_105, B_107]: (~r2_hidden(A_105, k2_tarski(A_105, B_107)) | k2_tarski(A_105, B_107)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_225, c_285])).
% 4.85/1.98  tff(c_291, plain, (![A_105, B_107]: (k2_tarski(A_105, B_107)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_289])).
% 4.85/1.98  tff(c_549, plain, (![A_77, B_76]: ('#skF_5'(k2_tarski(A_77, B_76))=B_76 | '#skF_5'(k2_tarski(A_77, B_76))=A_77)), inference(negUnitSimplification, [status(thm)], [c_291, c_147])).
% 4.85/1.98  tff(c_708, plain, (![B_193]: ('#skF_5'(k2_tarski(B_193, B_193))=B_193)), inference(factorization, [status(thm), theory('equality')], [c_549])).
% 4.85/1.98  tff(c_226, plain, (![C_97, A_98, D_99, E_100]: (~r2_hidden(C_97, A_98) | k3_mcart_1(C_97, D_99, E_100)!='#skF_5'(A_98) | k1_xboole_0=A_98)), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.85/1.98  tff(c_237, plain, (![D_12, D_99, E_100, B_8]: (k3_mcart_1(D_12, D_99, E_100)!='#skF_5'(k2_tarski(D_12, B_8)) | k2_tarski(D_12, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_226])).
% 4.85/1.98  tff(c_503, plain, (![D_12, D_99, E_100, B_8]: (k3_mcart_1(D_12, D_99, E_100)!='#skF_5'(k2_tarski(D_12, B_8)))), inference(negUnitSimplification, [status(thm)], [c_291, c_237])).
% 4.85/1.98  tff(c_728, plain, (![B_193, D_99, E_100]: (k3_mcart_1(B_193, D_99, E_100)!=B_193)), inference(superposition, [status(thm), theory('equality')], [c_708, c_503])).
% 4.85/1.98  tff(c_66, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.85/1.98  tff(c_189, plain, (k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_66])).
% 4.85/1.98  tff(c_1300, plain, (![A_289, B_290, C_291, D_292]: (k3_mcart_1(k5_mcart_1(A_289, B_290, C_291, D_292), k6_mcart_1(A_289, B_290, C_291, D_292), k7_mcart_1(A_289, B_290, C_291, D_292))=D_292 | ~m1_subset_1(D_292, k3_zfmisc_1(A_289, B_290, C_291)) | k1_xboole_0=C_291 | k1_xboole_0=B_290 | k1_xboole_0=A_289)), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.85/1.98  tff(c_1369, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_189, c_1300])).
% 4.85/1.98  tff(c_1377, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1369])).
% 4.85/1.98  tff(c_1379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_70, c_728, c_1377])).
% 4.85/1.98  tff(c_1380, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_66])).
% 4.85/1.98  tff(c_1473, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_1380])).
% 4.85/1.98  tff(c_2472, plain, (![A_494, B_495, C_496, D_497]: (k3_mcart_1(k5_mcart_1(A_494, B_495, C_496, D_497), k6_mcart_1(A_494, B_495, C_496, D_497), k7_mcart_1(A_494, B_495, C_496, D_497))=D_497 | ~m1_subset_1(D_497, k3_zfmisc_1(A_494, B_495, C_496)) | k1_xboole_0=C_496 | k1_xboole_0=B_495 | k1_xboole_0=A_494)), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.85/1.98  tff(c_2541, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1473, c_2472])).
% 4.85/1.98  tff(c_2549, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2541])).
% 4.85/1.98  tff(c_2551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_70, c_167, c_2549])).
% 4.85/1.98  tff(c_2552, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_1380])).
% 4.85/1.98  tff(c_3683, plain, (![A_691, B_692, C_693, D_694]: (k3_mcart_1(k5_mcart_1(A_691, B_692, C_693, D_694), k6_mcart_1(A_691, B_692, C_693, D_694), k7_mcart_1(A_691, B_692, C_693, D_694))=D_694 | ~m1_subset_1(D_694, k3_zfmisc_1(A_691, B_692, C_693)) | k1_xboole_0=C_693 | k1_xboole_0=B_692 | k1_xboole_0=A_691)), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.85/1.98  tff(c_3752, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2552, c_3683])).
% 4.85/1.98  tff(c_3760, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3752])).
% 4.85/1.98  tff(c_3762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_70, c_2991, c_3760])).
% 4.85/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.98  
% 4.85/1.98  Inference rules
% 4.85/1.98  ----------------------
% 4.85/1.98  #Ref     : 18
% 4.85/1.98  #Sup     : 829
% 4.85/1.98  #Fact    : 12
% 4.85/1.98  #Define  : 0
% 4.85/1.98  #Split   : 2
% 4.85/1.98  #Chain   : 0
% 4.85/1.98  #Close   : 0
% 4.85/1.98  
% 4.85/1.98  Ordering : KBO
% 4.85/1.98  
% 4.85/1.98  Simplification rules
% 4.85/1.98  ----------------------
% 4.85/1.98  #Subsume      : 202
% 4.85/1.98  #Demod        : 210
% 4.85/1.98  #Tautology    : 237
% 4.85/1.98  #SimpNegUnit  : 107
% 4.85/1.98  #BackRed      : 0
% 4.85/1.98  
% 4.85/1.98  #Partial instantiations: 0
% 4.85/1.98  #Strategies tried      : 1
% 4.85/1.98  
% 4.85/1.98  Timing (in seconds)
% 4.85/1.98  ----------------------
% 4.85/1.99  Preprocessing        : 0.36
% 4.85/1.99  Parsing              : 0.18
% 4.85/1.99  CNF conversion       : 0.03
% 4.85/1.99  Main loop            : 0.82
% 4.85/1.99  Inferencing          : 0.30
% 5.19/1.99  Reduction            : 0.25
% 5.19/1.99  Demodulation         : 0.16
% 5.19/1.99  BG Simplification    : 0.05
% 5.19/1.99  Subsumption          : 0.16
% 5.19/1.99  Abstraction          : 0.06
% 5.19/1.99  MUC search           : 0.00
% 5.19/1.99  Cooper               : 0.00
% 5.19/1.99  Total                : 1.21
% 5.19/1.99  Index Insertion      : 0.00
% 5.19/1.99  Index Deletion       : 0.00
% 5.19/1.99  Index Matching       : 0.00
% 5.19/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
