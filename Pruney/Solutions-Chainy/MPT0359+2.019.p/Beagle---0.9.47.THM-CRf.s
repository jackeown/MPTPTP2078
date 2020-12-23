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
% DateTime   : Thu Dec  3 09:56:11 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 236 expanded)
%              Number of leaves         :   35 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  116 ( 341 expanded)
%              Number of equality atoms :   57 ( 160 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_16,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_52])).

tff(c_225,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_59,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_58])).

tff(c_290,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_59])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_292,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_50])).

tff(c_48,plain,(
    ! [A_29] : ~ v1_xboole_0(k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_379,plain,(
    ! [B_60,A_61] :
      ( r2_hidden(B_60,A_61)
      | ~ m1_subset_1(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_383,plain,(
    ! [B_60,A_19] :
      ( r1_tarski(B_60,A_19)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_379,c_24])).

tff(c_442,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_383])).

tff(c_450,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_292,c_442])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_455,plain,(
    k3_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_450,c_14])).

tff(c_475,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_494,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_475])).

tff(c_515,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_494])).

tff(c_618,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(A_76,B_77) = k3_subset_1(A_76,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_624,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_292,c_618])).

tff(c_631,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_624])).

tff(c_291,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_225])).

tff(c_633,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_291])).

tff(c_636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_633])).

tff(c_637,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_131,plain,(
    ! [B_37,A_38] : k5_xboole_0(B_37,A_38) = k5_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_147,plain,(
    ! [A_38] : k5_xboole_0(k1_xboole_0,A_38) = A_38 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_18])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1662,plain,(
    ! [A_127,B_128] :
      ( k4_xboole_0(A_127,B_128) = k3_subset_1(A_127,B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1675,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1662])).

tff(c_1014,plain,(
    ! [B_104,A_105] :
      ( r2_hidden(B_104,A_105)
      | ~ m1_subset_1(B_104,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1018,plain,(
    ! [B_104,A_19] :
      ( r1_tarski(B_104,A_19)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_1014,c_24])).

tff(c_1686,plain,(
    ! [B_129,A_130] :
      ( r1_tarski(B_129,A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_130)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1018])).

tff(c_1699,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1686])).

tff(c_1703,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1699,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1057,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k3_xboole_0(A_108,B_109)) = k4_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1893,plain,(
    ! [B_141,A_142] : k5_xboole_0(B_141,k3_xboole_0(A_142,B_141)) = k4_xboole_0(B_141,A_142) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1057])).

tff(c_1944,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1703,c_1893])).

tff(c_1981,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1675,c_1944])).

tff(c_2029,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k3_subset_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1981])).

tff(c_645,plain,(
    ! [A_80,B_81] : r1_xboole_0(k3_xboole_0(A_80,B_81),k5_xboole_0(A_80,B_81)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_660,plain,(
    ! [A_1,B_2] : r1_xboole_0(k3_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_645])).

tff(c_1707,plain,(
    r1_xboole_0('#skF_4',k5_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1703,c_660])).

tff(c_1716,plain,(
    r1_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1707])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1726,plain,(
    k3_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1716,c_6])).

tff(c_2190,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2029,c_1726])).

tff(c_640,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_637,c_59])).

tff(c_871,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_878,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_640,c_871])).

tff(c_1002,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_878])).

tff(c_2266,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2190,c_1002])).

tff(c_1191,plain,(
    ! [A_116,B_117,C_118] : k5_xboole_0(k5_xboole_0(A_116,B_117),C_118) = k5_xboole_0(A_116,k5_xboole_0(B_117,C_118)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1261,plain,(
    ! [A_18,C_118] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_118)) = k5_xboole_0(k1_xboole_0,C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1191])).

tff(c_1274,plain,(
    ! [A_18,C_118] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_118)) = C_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1261])).

tff(c_1275,plain,(
    ! [A_119,C_120] : k5_xboole_0(A_119,k5_xboole_0(A_119,C_120)) = C_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_1261])).

tff(c_1347,plain,(
    ! [A_121,B_122] : k5_xboole_0(A_121,k5_xboole_0(B_122,A_121)) = B_122 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1275])).

tff(c_1386,plain,(
    ! [A_18,C_118] : k5_xboole_0(k5_xboole_0(A_18,C_118),C_118) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_1274,c_1347])).

tff(c_1998,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1981,c_1386])).

tff(c_2292,plain,(
    k5_xboole_0(k1_xboole_0,'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2266,c_1998])).

tff(c_2302,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_2292])).

tff(c_2304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_637,c_2302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:52:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/2.28  
% 4.50/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/2.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.50/2.29  
% 4.50/2.29  %Foreground sorts:
% 4.50/2.29  
% 4.50/2.29  
% 4.50/2.29  %Background operators:
% 4.50/2.29  
% 4.50/2.29  
% 4.50/2.29  %Foreground operators:
% 4.50/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.50/2.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.50/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/2.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.50/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/2.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.50/2.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.50/2.29  tff('#skF_3', type, '#skF_3': $i).
% 4.50/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.50/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/2.29  tff('#skF_4', type, '#skF_4': $i).
% 4.50/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/2.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.50/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/2.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.50/2.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.50/2.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.50/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.50/2.29  
% 4.80/2.31  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.80/2.31  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.80/2.31  tff(f_71, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.80/2.31  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 4.80/2.31  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.80/2.31  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.80/2.31  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.80/2.31  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.80/2.31  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.80/2.31  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.80/2.31  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.80/2.31  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.80/2.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.80/2.31  tff(f_35, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 4.80/2.31  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.80/2.31  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.80/2.31  tff(c_16, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.80/2.31  tff(c_22, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.80/2.31  tff(c_44, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.80/2.31  tff(c_52, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.80/2.31  tff(c_60, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_52])).
% 4.80/2.31  tff(c_225, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 4.80/2.31  tff(c_58, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.80/2.31  tff(c_59, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_58])).
% 4.80/2.31  tff(c_290, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_225, c_59])).
% 4.80/2.31  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.80/2.31  tff(c_292, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_50])).
% 4.80/2.31  tff(c_48, plain, (![A_29]: (~v1_xboole_0(k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.80/2.31  tff(c_379, plain, (![B_60, A_61]: (r2_hidden(B_60, A_61) | ~m1_subset_1(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.80/2.31  tff(c_24, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.80/2.31  tff(c_383, plain, (![B_60, A_19]: (r1_tarski(B_60, A_19) | ~m1_subset_1(B_60, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_379, c_24])).
% 4.80/2.31  tff(c_442, plain, (![B_66, A_67]: (r1_tarski(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)))), inference(negUnitSimplification, [status(thm)], [c_48, c_383])).
% 4.80/2.31  tff(c_450, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_292, c_442])).
% 4.80/2.31  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.80/2.31  tff(c_455, plain, (k3_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_450, c_14])).
% 4.80/2.31  tff(c_475, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.80/2.31  tff(c_494, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_455, c_475])).
% 4.80/2.31  tff(c_515, plain, (k4_xboole_0('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_494])).
% 4.80/2.31  tff(c_618, plain, (![A_76, B_77]: (k4_xboole_0(A_76, B_77)=k3_subset_1(A_76, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.80/2.31  tff(c_624, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_292, c_618])).
% 4.80/2.31  tff(c_631, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_515, c_624])).
% 4.80/2.31  tff(c_291, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_225])).
% 4.80/2.31  tff(c_633, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_631, c_291])).
% 4.80/2.31  tff(c_636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_633])).
% 4.80/2.31  tff(c_637, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 4.80/2.31  tff(c_131, plain, (![B_37, A_38]: (k5_xboole_0(B_37, A_38)=k5_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.80/2.31  tff(c_18, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.80/2.31  tff(c_147, plain, (![A_38]: (k5_xboole_0(k1_xboole_0, A_38)=A_38)), inference(superposition, [status(thm), theory('equality')], [c_131, c_18])).
% 4.80/2.31  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.80/2.31  tff(c_1662, plain, (![A_127, B_128]: (k4_xboole_0(A_127, B_128)=k3_subset_1(A_127, B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.80/2.31  tff(c_1675, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1662])).
% 4.80/2.31  tff(c_1014, plain, (![B_104, A_105]: (r2_hidden(B_104, A_105) | ~m1_subset_1(B_104, A_105) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.80/2.31  tff(c_1018, plain, (![B_104, A_19]: (r1_tarski(B_104, A_19) | ~m1_subset_1(B_104, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_1014, c_24])).
% 4.80/2.31  tff(c_1686, plain, (![B_129, A_130]: (r1_tarski(B_129, A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(A_130)))), inference(negUnitSimplification, [status(thm)], [c_48, c_1018])).
% 4.80/2.31  tff(c_1699, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1686])).
% 4.80/2.31  tff(c_1703, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1699, c_14])).
% 4.80/2.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.80/2.31  tff(c_1057, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k3_xboole_0(A_108, B_109))=k4_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.80/2.31  tff(c_1893, plain, (![B_141, A_142]: (k5_xboole_0(B_141, k3_xboole_0(A_142, B_141))=k4_xboole_0(B_141, A_142))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1057])).
% 4.80/2.31  tff(c_1944, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1703, c_1893])).
% 4.80/2.31  tff(c_1981, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1675, c_1944])).
% 4.80/2.31  tff(c_2029, plain, (k5_xboole_0('#skF_4', '#skF_3')=k3_subset_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4, c_1981])).
% 4.80/2.31  tff(c_645, plain, (![A_80, B_81]: (r1_xboole_0(k3_xboole_0(A_80, B_81), k5_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/2.31  tff(c_660, plain, (![A_1, B_2]: (r1_xboole_0(k3_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_645])).
% 4.80/2.31  tff(c_1707, plain, (r1_xboole_0('#skF_4', k5_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1703, c_660])).
% 4.80/2.31  tff(c_1716, plain, (r1_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1707])).
% 4.80/2.31  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.80/2.31  tff(c_1726, plain, (k3_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1716, c_6])).
% 4.80/2.31  tff(c_2190, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2029, c_1726])).
% 4.80/2.31  tff(c_640, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_637, c_59])).
% 4.80/2.31  tff(c_871, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.80/2.31  tff(c_878, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_640, c_871])).
% 4.80/2.31  tff(c_1002, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2, c_878])).
% 4.80/2.31  tff(c_2266, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2190, c_1002])).
% 4.80/2.31  tff(c_1191, plain, (![A_116, B_117, C_118]: (k5_xboole_0(k5_xboole_0(A_116, B_117), C_118)=k5_xboole_0(A_116, k5_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.80/2.31  tff(c_1261, plain, (![A_18, C_118]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_118))=k5_xboole_0(k1_xboole_0, C_118))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1191])).
% 4.80/2.31  tff(c_1274, plain, (![A_18, C_118]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_118))=C_118)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_1261])).
% 4.80/2.31  tff(c_1275, plain, (![A_119, C_120]: (k5_xboole_0(A_119, k5_xboole_0(A_119, C_120))=C_120)), inference(demodulation, [status(thm), theory('equality')], [c_147, c_1261])).
% 4.80/2.31  tff(c_1347, plain, (![A_121, B_122]: (k5_xboole_0(A_121, k5_xboole_0(B_122, A_121))=B_122)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1275])).
% 4.80/2.31  tff(c_1386, plain, (![A_18, C_118]: (k5_xboole_0(k5_xboole_0(A_18, C_118), C_118)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_1274, c_1347])).
% 4.80/2.31  tff(c_1998, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1981, c_1386])).
% 4.80/2.31  tff(c_2292, plain, (k5_xboole_0(k1_xboole_0, '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2266, c_1998])).
% 4.80/2.31  tff(c_2302, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_2292])).
% 4.80/2.31  tff(c_2304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_637, c_2302])).
% 4.80/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/2.31  
% 4.80/2.31  Inference rules
% 4.80/2.31  ----------------------
% 4.80/2.31  #Ref     : 0
% 4.80/2.31  #Sup     : 549
% 4.80/2.31  #Fact    : 0
% 4.80/2.31  #Define  : 0
% 4.80/2.31  #Split   : 1
% 4.80/2.31  #Chain   : 0
% 4.80/2.32  #Close   : 0
% 4.80/2.32  
% 4.80/2.32  Ordering : KBO
% 4.80/2.32  
% 4.80/2.32  Simplification rules
% 4.80/2.32  ----------------------
% 4.80/2.32  #Subsume      : 12
% 4.80/2.32  #Demod        : 396
% 4.80/2.32  #Tautology    : 387
% 4.80/2.32  #SimpNegUnit  : 7
% 4.80/2.32  #BackRed      : 24
% 4.80/2.32  
% 4.80/2.32  #Partial instantiations: 0
% 4.80/2.32  #Strategies tried      : 1
% 4.80/2.32  
% 4.80/2.32  Timing (in seconds)
% 4.80/2.32  ----------------------
% 4.80/2.32  Preprocessing        : 0.50
% 4.80/2.32  Parsing              : 0.25
% 4.80/2.32  CNF conversion       : 0.03
% 4.80/2.32  Main loop            : 0.89
% 4.80/2.32  Inferencing          : 0.28
% 4.80/2.32  Reduction            : 0.37
% 4.80/2.32  Demodulation         : 0.30
% 4.80/2.32  BG Simplification    : 0.04
% 4.80/2.32  Subsumption          : 0.13
% 4.80/2.32  Abstraction          : 0.04
% 4.80/2.32  MUC search           : 0.00
% 4.80/2.32  Cooper               : 0.00
% 4.80/2.32  Total                : 1.46
% 4.80/2.32  Index Insertion      : 0.00
% 4.80/2.32  Index Deletion       : 0.00
% 4.80/2.32  Index Matching       : 0.00
% 4.80/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
