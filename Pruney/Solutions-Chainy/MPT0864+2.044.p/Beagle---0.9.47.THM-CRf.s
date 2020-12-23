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
% DateTime   : Thu Dec  3 10:09:14 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.38s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 281 expanded)
%              Number of leaves         :   36 ( 104 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 459 expanded)
%              Number of equality atoms :   70 ( 304 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
     => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : ~ v1_xboole_0(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_102,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_27,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(c_72,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_13952,plain,(
    ! [A_5644,B_5645] : k2_mcart_1(k4_tarski(A_5644,B_5645)) = B_5645 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_13961,plain,(
    k2_mcart_1('#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_13952])).

tff(c_8,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_183,plain,(
    ! [C_56,B_57] : r1_tarski(k1_tarski(C_56),k2_tarski(B_57,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_186,plain,(
    ! [A_4] : r1_tarski(k1_tarski(A_4),k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_183])).

tff(c_111,plain,(
    ! [A_48,B_49] : k1_mcart_1(k4_tarski(A_48,B_49)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_120,plain,(
    k1_mcart_1('#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_111])).

tff(c_70,plain,
    ( k2_mcart_1('#skF_2') = '#skF_2'
    | k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_123,plain,(
    k1_mcart_1('#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_128,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_123])).

tff(c_135,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_72])).

tff(c_24,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7369,plain,(
    ! [C_2771,B_2772,D_2773] :
      ( r2_hidden(k4_tarski(C_2771,B_2772),k2_zfmisc_1(k1_tarski(C_2771),D_2773))
      | ~ r2_hidden(B_2772,D_2773) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10731,plain,(
    ! [C_4170,B_4171] :
      ( r2_hidden(k4_tarski(C_4170,B_4171),k1_xboole_0)
      | ~ r2_hidden(B_4171,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7369])).

tff(c_7096,plain,(
    ! [C_2712,A_2713,B_2714,D_2715] :
      ( C_2712 = A_2713
      | ~ r2_hidden(k4_tarski(A_2713,B_2714),k2_zfmisc_1(k1_tarski(C_2712),D_2715)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7108,plain,(
    ! [C_2712,A_2713,B_2714] :
      ( C_2712 = A_2713
      | ~ r2_hidden(k4_tarski(A_2713,B_2714),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7096])).

tff(c_10755,plain,(
    ! [C_4170,C_2712,B_4171] :
      ( C_4170 = C_2712
      | ~ r2_hidden(B_4171,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10731,c_7108])).

tff(c_10780,plain,(
    ! [B_4171] : ~ r2_hidden(B_4171,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_10755])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7137,plain,(
    ! [A_2724,C_2725,B_2726] :
      ( r2_hidden(A_2724,C_2725)
      | k3_xboole_0(k2_tarski(A_2724,B_2726),C_2725) != k2_tarski(A_2724,B_2726) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7146,plain,(
    ! [A_2727,B_2728] :
      ( r2_hidden(A_2727,k1_xboole_0)
      | k2_tarski(A_2727,B_2728) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7137])).

tff(c_7148,plain,(
    ! [A_4] :
      ( r2_hidden(A_4,k1_xboole_0)
      | k1_tarski(A_4) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_7146])).

tff(c_10823,plain,(
    ! [A_4] : k1_tarski(A_4) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10780,c_7148])).

tff(c_263,plain,(
    ! [A_81,B_82] : k2_zfmisc_1(k1_tarski(A_81),k1_tarski(B_82)) = k1_tarski(k4_tarski(A_81,B_82)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    ! [A_22,B_23] :
      ( ~ r1_tarski(A_22,k2_zfmisc_1(A_22,B_23))
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_275,plain,(
    ! [A_81,B_82] :
      ( ~ r1_tarski(k1_tarski(A_81),k1_tarski(k4_tarski(A_81,B_82)))
      | k1_tarski(A_81) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_44])).

tff(c_11216,plain,(
    ! [A_4211,B_4212] : ~ r1_tarski(k1_tarski(A_4211),k1_tarski(k4_tarski(A_4211,B_4212))) ),
    inference(negUnitSimplification,[status(thm)],[c_10823,c_275])).

tff(c_11219,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_11216])).

tff(c_11222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_11219])).

tff(c_11224,plain,(
    ! [C_4214,C_4213] : C_4214 = C_4213 ),
    inference(splitRight,[status(thm)],[c_10755])).

tff(c_108,plain,(
    ! [A_46,B_47] : ~ v1_xboole_0(k4_tarski(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_110,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_108])).

tff(c_134,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_110])).

tff(c_559,plain,(
    ! [C_149,B_150,D_151] :
      ( r2_hidden(k4_tarski(C_149,B_150),k2_zfmisc_1(k1_tarski(C_149),D_151))
      | ~ r2_hidden(B_150,D_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3695,plain,(
    ! [C_1417,B_1418] :
      ( r2_hidden(k4_tarski(C_1417,B_1418),k1_xboole_0)
      | ~ r2_hidden(B_1418,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_559])).

tff(c_347,plain,(
    ! [C_99,A_100,B_101,D_102] :
      ( C_99 = A_100
      | ~ r2_hidden(k4_tarski(A_100,B_101),k2_zfmisc_1(k1_tarski(C_99),D_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_359,plain,(
    ! [C_99,A_100,B_101] :
      ( C_99 = A_100
      | ~ r2_hidden(k4_tarski(A_100,B_101),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_347])).

tff(c_3715,plain,(
    ! [C_99,C_1417,B_1418] :
      ( C_99 = C_1417
      | ~ r2_hidden(B_1418,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3695,c_359])).

tff(c_3763,plain,(
    ! [B_1418] : ~ r2_hidden(B_1418,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3715])).

tff(c_389,plain,(
    ! [A_110,C_111,B_112] :
      ( r2_hidden(A_110,C_111)
      | k3_xboole_0(k2_tarski(A_110,B_112),C_111) != k2_tarski(A_110,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_398,plain,(
    ! [A_113,B_114] :
      ( r2_hidden(A_113,k1_xboole_0)
      | k2_tarski(A_113,B_114) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_389])).

tff(c_400,plain,(
    ! [A_4] :
      ( r2_hidden(A_4,k1_xboole_0)
      | k1_tarski(A_4) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_398])).

tff(c_3766,plain,(
    ! [A_4] : k1_tarski(A_4) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3763,c_400])).

tff(c_3908,plain,(
    ! [A_1438,B_1439] : ~ r1_tarski(k1_tarski(A_1438),k1_tarski(k4_tarski(A_1438,B_1439))) ),
    inference(negUnitSimplification,[status(thm)],[c_3766,c_275])).

tff(c_3911,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_3908])).

tff(c_3914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_3911])).

tff(c_5571,plain,(
    ! [C_1443] : C_1443 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3715])).

tff(c_56,plain,(
    ! [B_33,A_32] :
      ( r2_hidden(B_33,A_32)
      | ~ m1_subset_1(B_33,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_62,plain,(
    ! [A_34] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_323,plain,(
    ! [A_92,C_93,B_94] :
      ( m1_subset_1(A_92,C_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_93))
      | ~ r2_hidden(A_92,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_331,plain,(
    ! [A_95,A_96] :
      ( m1_subset_1(A_95,A_96)
      | ~ r2_hidden(A_95,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_62,c_323])).

tff(c_335,plain,(
    ! [B_33,A_96] :
      ( m1_subset_1(B_33,A_96)
      | ~ m1_subset_1(B_33,k1_xboole_0)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_56,c_331])).

tff(c_336,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_5573,plain,(
    v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5571,c_336])).

tff(c_7071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_5573])).

tff(c_7073,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_12442,plain,(
    ! [C_4214] : ~ v1_xboole_0(C_4214) ),
    inference(superposition,[status(thm),theory(equality)],[c_11224,c_7073])).

tff(c_2,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_13931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12442,c_2])).

tff(c_13932,plain,(
    k2_mcart_1('#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_13964,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13961,c_13932])).

tff(c_13933,plain,(
    k1_mcart_1('#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_13947,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_13933])).

tff(c_13970,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13964,c_13947])).

tff(c_14004,plain,(
    ! [C_5649,B_5650] : r1_tarski(k1_tarski(C_5649),k2_tarski(B_5650,C_5649)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14007,plain,(
    ! [A_4] : r1_tarski(k1_tarski(A_4),k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_14004])).

tff(c_13973,plain,(
    k4_tarski('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13964,c_72])).

tff(c_14083,plain,(
    ! [A_5674,B_5675] : k2_zfmisc_1(k1_tarski(A_5674),k1_tarski(B_5675)) = k1_tarski(k4_tarski(A_5674,B_5675)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [A_22,B_23] :
      ( ~ r1_tarski(A_22,k2_zfmisc_1(B_23,A_22))
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14219,plain,(
    ! [B_5705,A_5706] :
      ( ~ r1_tarski(k1_tarski(B_5705),k1_tarski(k4_tarski(A_5706,B_5705)))
      | k1_tarski(B_5705) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14083,c_42])).

tff(c_14222,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13973,c_14219])).

tff(c_14224,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14007,c_14222])).

tff(c_14357,plain,(
    ! [A_5708,C_5709,B_5710] :
      ( r2_hidden(A_5708,C_5709)
      | k3_xboole_0(k2_tarski(A_5708,B_5710),C_5709) != k2_tarski(A_5708,B_5710) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14447,plain,(
    ! [A_5712,B_5713] :
      ( r2_hidden(A_5712,k1_xboole_0)
      | k2_tarski(A_5712,B_5713) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_14357])).

tff(c_14450,plain,(
    ! [A_5714] :
      ( r2_hidden(A_5714,k1_xboole_0)
      | k1_tarski(A_5714) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_14447])).

tff(c_14115,plain,(
    ! [C_5681,A_5682,B_5683,D_5684] :
      ( C_5681 = A_5682
      | ~ r2_hidden(k4_tarski(A_5682,B_5683),k2_zfmisc_1(k1_tarski(C_5681),D_5684)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14129,plain,(
    ! [C_5685,A_5686,B_5687] :
      ( C_5685 = A_5686
      | ~ r2_hidden(k4_tarski(A_5686,B_5687),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_14115])).

tff(c_14134,plain,(
    ! [C_5685] :
      ( C_5685 = '#skF_3'
      | ~ r2_hidden('#skF_4',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13973,c_14129])).

tff(c_14137,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_14134])).

tff(c_14456,plain,(
    k1_tarski('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14450,c_14137])).

tff(c_14469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14224,c_14456])).

tff(c_14483,plain,(
    ! [C_5717] : C_5717 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14134])).

tff(c_14553,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_14483,c_13973])).

tff(c_14598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13970,c_14553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.38/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.29  
% 6.38/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.38/2.29  
% 6.38/2.29  %Foreground sorts:
% 6.38/2.29  
% 6.38/2.29  
% 6.38/2.29  %Background operators:
% 6.38/2.29  
% 6.38/2.29  
% 6.38/2.29  %Foreground operators:
% 6.38/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.38/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.38/2.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.38/2.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.38/2.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.38/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.38/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.38/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.38/2.29  tff('#skF_2', type, '#skF_2': $i).
% 6.38/2.29  tff('#skF_3', type, '#skF_3': $i).
% 6.38/2.29  tff('#skF_1', type, '#skF_1': $i).
% 6.38/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.38/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.38/2.29  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.38/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.38/2.29  tff('#skF_4', type, '#skF_4': $i).
% 6.38/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.38/2.29  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.38/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.38/2.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.38/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.38/2.29  
% 6.38/2.31  tff(f_122, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 6.38/2.31  tff(f_112, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 6.38/2.31  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.38/2.31  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 6.38/2.31  tff(f_57, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.38/2.31  tff(f_63, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 6.38/2.31  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.38/2.31  tff(f_87, axiom, (![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 6.38/2.31  tff(f_79, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 6.38/2.31  tff(f_77, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 6.38/2.31  tff(f_36, axiom, (![A, B]: ~v1_xboole_0(k4_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_zfmisc_1)).
% 6.38/2.31  tff(f_100, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.38/2.31  tff(f_102, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.38/2.31  tff(f_108, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.38/2.31  tff(f_27, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 6.38/2.31  tff(c_72, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.38/2.31  tff(c_13952, plain, (![A_5644, B_5645]: (k2_mcart_1(k4_tarski(A_5644, B_5645))=B_5645)), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.38/2.31  tff(c_13961, plain, (k2_mcart_1('#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_72, c_13952])).
% 6.38/2.31  tff(c_8, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.38/2.31  tff(c_183, plain, (![C_56, B_57]: (r1_tarski(k1_tarski(C_56), k2_tarski(B_57, C_56)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.38/2.31  tff(c_186, plain, (![A_4]: (r1_tarski(k1_tarski(A_4), k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_183])).
% 6.38/2.31  tff(c_111, plain, (![A_48, B_49]: (k1_mcart_1(k4_tarski(A_48, B_49))=A_48)), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.38/2.31  tff(c_120, plain, (k1_mcart_1('#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_72, c_111])).
% 6.38/2.31  tff(c_70, plain, (k2_mcart_1('#skF_2')='#skF_2' | k1_mcart_1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.38/2.31  tff(c_123, plain, (k1_mcart_1('#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_70])).
% 6.38/2.31  tff(c_128, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_123])).
% 6.38/2.31  tff(c_135, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_72])).
% 6.38/2.31  tff(c_24, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.38/2.31  tff(c_7369, plain, (![C_2771, B_2772, D_2773]: (r2_hidden(k4_tarski(C_2771, B_2772), k2_zfmisc_1(k1_tarski(C_2771), D_2773)) | ~r2_hidden(B_2772, D_2773))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.38/2.31  tff(c_10731, plain, (![C_4170, B_4171]: (r2_hidden(k4_tarski(C_4170, B_4171), k1_xboole_0) | ~r2_hidden(B_4171, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_7369])).
% 6.38/2.31  tff(c_7096, plain, (![C_2712, A_2713, B_2714, D_2715]: (C_2712=A_2713 | ~r2_hidden(k4_tarski(A_2713, B_2714), k2_zfmisc_1(k1_tarski(C_2712), D_2715)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.38/2.31  tff(c_7108, plain, (![C_2712, A_2713, B_2714]: (C_2712=A_2713 | ~r2_hidden(k4_tarski(A_2713, B_2714), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_7096])).
% 6.38/2.31  tff(c_10755, plain, (![C_4170, C_2712, B_4171]: (C_4170=C_2712 | ~r2_hidden(B_4171, k1_xboole_0))), inference(resolution, [status(thm)], [c_10731, c_7108])).
% 6.38/2.31  tff(c_10780, plain, (![B_4171]: (~r2_hidden(B_4171, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_10755])).
% 6.38/2.31  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.38/2.31  tff(c_7137, plain, (![A_2724, C_2725, B_2726]: (r2_hidden(A_2724, C_2725) | k3_xboole_0(k2_tarski(A_2724, B_2726), C_2725)!=k2_tarski(A_2724, B_2726))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.38/2.31  tff(c_7146, plain, (![A_2727, B_2728]: (r2_hidden(A_2727, k1_xboole_0) | k2_tarski(A_2727, B_2728)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_7137])).
% 6.38/2.31  tff(c_7148, plain, (![A_4]: (r2_hidden(A_4, k1_xboole_0) | k1_tarski(A_4)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_7146])).
% 6.38/2.31  tff(c_10823, plain, (![A_4]: (k1_tarski(A_4)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_10780, c_7148])).
% 6.38/2.31  tff(c_263, plain, (![A_81, B_82]: (k2_zfmisc_1(k1_tarski(A_81), k1_tarski(B_82))=k1_tarski(k4_tarski(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.38/2.31  tff(c_44, plain, (![A_22, B_23]: (~r1_tarski(A_22, k2_zfmisc_1(A_22, B_23)) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.38/2.31  tff(c_275, plain, (![A_81, B_82]: (~r1_tarski(k1_tarski(A_81), k1_tarski(k4_tarski(A_81, B_82))) | k1_tarski(A_81)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_263, c_44])).
% 6.38/2.31  tff(c_11216, plain, (![A_4211, B_4212]: (~r1_tarski(k1_tarski(A_4211), k1_tarski(k4_tarski(A_4211, B_4212))))), inference(negUnitSimplification, [status(thm)], [c_10823, c_275])).
% 6.38/2.31  tff(c_11219, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_11216])).
% 6.38/2.31  tff(c_11222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_11219])).
% 6.38/2.31  tff(c_11224, plain, (![C_4214, C_4213]: (C_4214=C_4213)), inference(splitRight, [status(thm)], [c_10755])).
% 6.38/2.31  tff(c_108, plain, (![A_46, B_47]: (~v1_xboole_0(k4_tarski(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.38/2.31  tff(c_110, plain, (~v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72, c_108])).
% 6.38/2.31  tff(c_134, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_110])).
% 6.38/2.31  tff(c_559, plain, (![C_149, B_150, D_151]: (r2_hidden(k4_tarski(C_149, B_150), k2_zfmisc_1(k1_tarski(C_149), D_151)) | ~r2_hidden(B_150, D_151))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.38/2.31  tff(c_3695, plain, (![C_1417, B_1418]: (r2_hidden(k4_tarski(C_1417, B_1418), k1_xboole_0) | ~r2_hidden(B_1418, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_559])).
% 6.38/2.31  tff(c_347, plain, (![C_99, A_100, B_101, D_102]: (C_99=A_100 | ~r2_hidden(k4_tarski(A_100, B_101), k2_zfmisc_1(k1_tarski(C_99), D_102)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.38/2.31  tff(c_359, plain, (![C_99, A_100, B_101]: (C_99=A_100 | ~r2_hidden(k4_tarski(A_100, B_101), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_347])).
% 6.38/2.31  tff(c_3715, plain, (![C_99, C_1417, B_1418]: (C_99=C_1417 | ~r2_hidden(B_1418, k1_xboole_0))), inference(resolution, [status(thm)], [c_3695, c_359])).
% 6.38/2.31  tff(c_3763, plain, (![B_1418]: (~r2_hidden(B_1418, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_3715])).
% 6.38/2.31  tff(c_389, plain, (![A_110, C_111, B_112]: (r2_hidden(A_110, C_111) | k3_xboole_0(k2_tarski(A_110, B_112), C_111)!=k2_tarski(A_110, B_112))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.38/2.31  tff(c_398, plain, (![A_113, B_114]: (r2_hidden(A_113, k1_xboole_0) | k2_tarski(A_113, B_114)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_389])).
% 6.38/2.31  tff(c_400, plain, (![A_4]: (r2_hidden(A_4, k1_xboole_0) | k1_tarski(A_4)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_398])).
% 6.38/2.31  tff(c_3766, plain, (![A_4]: (k1_tarski(A_4)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_3763, c_400])).
% 6.38/2.31  tff(c_3908, plain, (![A_1438, B_1439]: (~r1_tarski(k1_tarski(A_1438), k1_tarski(k4_tarski(A_1438, B_1439))))), inference(negUnitSimplification, [status(thm)], [c_3766, c_275])).
% 6.38/2.31  tff(c_3911, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_3908])).
% 6.38/2.31  tff(c_3914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_3911])).
% 6.38/2.31  tff(c_5571, plain, (![C_1443]: (C_1443='#skF_3')), inference(splitRight, [status(thm)], [c_3715])).
% 6.38/2.31  tff(c_56, plain, (![B_33, A_32]: (r2_hidden(B_33, A_32) | ~m1_subset_1(B_33, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.38/2.31  tff(c_62, plain, (![A_34]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.38/2.31  tff(c_323, plain, (![A_92, C_93, B_94]: (m1_subset_1(A_92, C_93) | ~m1_subset_1(B_94, k1_zfmisc_1(C_93)) | ~r2_hidden(A_92, B_94))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.38/2.31  tff(c_331, plain, (![A_95, A_96]: (m1_subset_1(A_95, A_96) | ~r2_hidden(A_95, k1_xboole_0))), inference(resolution, [status(thm)], [c_62, c_323])).
% 6.38/2.31  tff(c_335, plain, (![B_33, A_96]: (m1_subset_1(B_33, A_96) | ~m1_subset_1(B_33, k1_xboole_0) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_331])).
% 6.38/2.31  tff(c_336, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_335])).
% 6.38/2.31  tff(c_5573, plain, (v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5571, c_336])).
% 6.38/2.31  tff(c_7071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_5573])).
% 6.38/2.31  tff(c_7073, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_335])).
% 6.38/2.31  tff(c_12442, plain, (![C_4214]: (~v1_xboole_0(C_4214))), inference(superposition, [status(thm), theory('equality')], [c_11224, c_7073])).
% 6.38/2.31  tff(c_2, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.38/2.31  tff(c_13931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12442, c_2])).
% 6.38/2.31  tff(c_13932, plain, (k2_mcart_1('#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_70])).
% 6.38/2.31  tff(c_13964, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13961, c_13932])).
% 6.38/2.31  tff(c_13933, plain, (k1_mcart_1('#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_70])).
% 6.38/2.31  tff(c_13947, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_13933])).
% 6.38/2.31  tff(c_13970, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13964, c_13947])).
% 6.38/2.31  tff(c_14004, plain, (![C_5649, B_5650]: (r1_tarski(k1_tarski(C_5649), k2_tarski(B_5650, C_5649)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.38/2.31  tff(c_14007, plain, (![A_4]: (r1_tarski(k1_tarski(A_4), k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_14004])).
% 6.38/2.31  tff(c_13973, plain, (k4_tarski('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13964, c_72])).
% 6.38/2.31  tff(c_14083, plain, (![A_5674, B_5675]: (k2_zfmisc_1(k1_tarski(A_5674), k1_tarski(B_5675))=k1_tarski(k4_tarski(A_5674, B_5675)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.38/2.31  tff(c_42, plain, (![A_22, B_23]: (~r1_tarski(A_22, k2_zfmisc_1(B_23, A_22)) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.38/2.31  tff(c_14219, plain, (![B_5705, A_5706]: (~r1_tarski(k1_tarski(B_5705), k1_tarski(k4_tarski(A_5706, B_5705))) | k1_tarski(B_5705)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14083, c_42])).
% 6.38/2.31  tff(c_14222, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13973, c_14219])).
% 6.38/2.31  tff(c_14224, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14007, c_14222])).
% 6.38/2.31  tff(c_14357, plain, (![A_5708, C_5709, B_5710]: (r2_hidden(A_5708, C_5709) | k3_xboole_0(k2_tarski(A_5708, B_5710), C_5709)!=k2_tarski(A_5708, B_5710))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.38/2.31  tff(c_14447, plain, (![A_5712, B_5713]: (r2_hidden(A_5712, k1_xboole_0) | k2_tarski(A_5712, B_5713)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_14357])).
% 6.38/2.31  tff(c_14450, plain, (![A_5714]: (r2_hidden(A_5714, k1_xboole_0) | k1_tarski(A_5714)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_14447])).
% 6.38/2.31  tff(c_14115, plain, (![C_5681, A_5682, B_5683, D_5684]: (C_5681=A_5682 | ~r2_hidden(k4_tarski(A_5682, B_5683), k2_zfmisc_1(k1_tarski(C_5681), D_5684)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.38/2.31  tff(c_14129, plain, (![C_5685, A_5686, B_5687]: (C_5685=A_5686 | ~r2_hidden(k4_tarski(A_5686, B_5687), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_14115])).
% 6.38/2.31  tff(c_14134, plain, (![C_5685]: (C_5685='#skF_3' | ~r2_hidden('#skF_4', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13973, c_14129])).
% 6.38/2.31  tff(c_14137, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_14134])).
% 6.38/2.31  tff(c_14456, plain, (k1_tarski('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_14450, c_14137])).
% 6.38/2.31  tff(c_14469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14224, c_14456])).
% 6.38/2.31  tff(c_14483, plain, (![C_5717]: (C_5717='#skF_3')), inference(splitRight, [status(thm)], [c_14134])).
% 6.38/2.31  tff(c_14553, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_14483, c_13973])).
% 6.38/2.31  tff(c_14598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13970, c_14553])).
% 6.38/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.31  
% 6.38/2.31  Inference rules
% 6.38/2.31  ----------------------
% 6.38/2.31  #Ref     : 0
% 6.38/2.31  #Sup     : 3444
% 6.38/2.31  #Fact    : 0
% 6.38/2.31  #Define  : 0
% 6.38/2.31  #Split   : 21
% 6.38/2.31  #Chain   : 0
% 6.38/2.31  #Close   : 0
% 6.38/2.31  
% 6.38/2.31  Ordering : KBO
% 6.38/2.31  
% 6.38/2.31  Simplification rules
% 6.38/2.31  ----------------------
% 6.38/2.31  #Subsume      : 462
% 6.38/2.31  #Demod        : 200
% 6.38/2.31  #Tautology    : 270
% 6.38/2.31  #SimpNegUnit  : 177
% 6.38/2.31  #BackRed      : 40
% 6.38/2.31  
% 6.38/2.31  #Partial instantiations: 5256
% 6.38/2.31  #Strategies tried      : 1
% 6.38/2.31  
% 6.38/2.31  Timing (in seconds)
% 6.38/2.31  ----------------------
% 6.38/2.31  Preprocessing        : 0.36
% 6.38/2.31  Parsing              : 0.18
% 6.38/2.31  CNF conversion       : 0.03
% 6.38/2.31  Main loop            : 1.18
% 6.38/2.31  Inferencing          : 0.51
% 6.38/2.31  Reduction            : 0.33
% 6.38/2.31  Demodulation         : 0.21
% 6.38/2.31  BG Simplification    : 0.05
% 6.38/2.31  Subsumption          : 0.19
% 6.38/2.31  Abstraction          : 0.06
% 6.38/2.31  MUC search           : 0.00
% 6.38/2.31  Cooper               : 0.00
% 6.38/2.31  Total                : 1.57
% 6.38/2.31  Index Insertion      : 0.00
% 6.38/2.31  Index Deletion       : 0.00
% 6.38/2.31  Index Matching       : 0.00
% 6.38/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
