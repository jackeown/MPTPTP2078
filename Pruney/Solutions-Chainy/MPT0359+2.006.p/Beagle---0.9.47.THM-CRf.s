%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:09 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 179 expanded)
%              Number of leaves         :   36 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 244 expanded)
%              Number of equality atoms :   65 ( 119 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_82,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_235,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_257,plain,(
    ! [A_51] : k3_xboole_0(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_235])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_266,plain,(
    ! [A_51] : k3_xboole_0(A_51,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_4])).

tff(c_22,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_485,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_517,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_485])).

tff(c_524,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_517])).

tff(c_48,plain,(
    ! [A_27] : k2_subset_1(A_27) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_62,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_63,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_148,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_149,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_54])).

tff(c_818,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_828,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_149,c_818])).

tff(c_832,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_828])).

tff(c_56,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_56])).

tff(c_228,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_148,c_64])).

tff(c_833,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_228])).

tff(c_836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_833])).

tff(c_838,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_52,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1172,plain,(
    ! [B_117,A_118] :
      ( r2_hidden(B_117,A_118)
      | ~ m1_subset_1(B_117,A_118)
      | v1_xboole_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [C_24,A_20] :
      ( r1_tarski(C_24,A_20)
      | ~ r2_hidden(C_24,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1179,plain,(
    ! [B_117,A_20] :
      ( r1_tarski(B_117,A_20)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_1172,c_28])).

tff(c_1184,plain,(
    ! [B_119,A_120] :
      ( r1_tarski(B_119,A_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_120)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1179])).

tff(c_1197,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1184])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1199,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1197,c_6])).

tff(c_1205,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_838,c_1199])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1061,plain,(
    ! [B_109,A_110] :
      ( B_109 = A_110
      | ~ r1_tarski(B_109,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1077,plain,(
    ! [A_111] :
      ( k1_xboole_0 = A_111
      | ~ r1_tarski(A_111,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_1061])).

tff(c_1127,plain,(
    ! [B_115] : k4_xboole_0(k1_xboole_0,B_115) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_1077])).

tff(c_26,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1132,plain,(
    ! [B_115] : k5_xboole_0(B_115,k1_xboole_0) = k2_xboole_0(B_115,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1127,c_26])).

tff(c_1147,plain,(
    ! [B_115] : k5_xboole_0(B_115,k1_xboole_0) = B_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1132])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_915,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(A_94,B_95) = A_94
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_941,plain,(
    ! [A_97] : k3_xboole_0(k1_xboole_0,A_97) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_915])).

tff(c_950,plain,(
    ! [A_97] : k3_xboole_0(A_97,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_941,c_4])).

tff(c_1207,plain,(
    ! [A_121,B_122] : k4_xboole_0(A_121,k4_xboole_0(A_121,B_122)) = k3_xboole_0(A_121,B_122) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1239,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1207])).

tff(c_1246,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_1239])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_930,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_915])).

tff(c_1412,plain,(
    ! [A_129,B_130] : k5_xboole_0(A_129,k3_xboole_0(A_129,B_130)) = k4_xboole_0(A_129,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1444,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_930,c_1412])).

tff(c_1457,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1246,c_1444])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1206,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1197,c_16])).

tff(c_1428,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_1412])).

tff(c_1540,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1457,c_1428])).

tff(c_1547,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1540,c_26])).

tff(c_1554,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_2,c_1547])).

tff(c_1485,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(A_132,B_133) = k3_subset_1(A_132,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1498,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1485])).

tff(c_1505,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_26])).

tff(c_1557,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1554,c_1505])).

tff(c_837,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_928,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_837,c_915])).

tff(c_1566,plain,(
    ! [A_134,B_135] : k5_xboole_0(A_134,k3_xboole_0(B_135,A_134)) = k4_xboole_0(A_134,B_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1412])).

tff(c_1597,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_1566])).

tff(c_1621,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_1597])).

tff(c_1670,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_20])).

tff(c_1676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1205,c_1670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  
% 3.07/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.07/1.48  
% 3.07/1.48  %Foreground sorts:
% 3.07/1.48  
% 3.07/1.48  
% 3.07/1.48  %Background operators:
% 3.07/1.48  
% 3.07/1.48  
% 3.07/1.48  %Foreground operators:
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.07/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.07/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.07/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.07/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.07/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.07/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.07/1.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.07/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.48  
% 3.07/1.50  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.07/1.50  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.07/1.50  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.07/1.50  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.07/1.50  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.07/1.50  tff(f_75, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.07/1.50  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 3.07/1.50  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.07/1.50  tff(f_82, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.07/1.50  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.07/1.50  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.07/1.50  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.07/1.50  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.07/1.50  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.07/1.50  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.07/1.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.07/1.50  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.07/1.50  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.07/1.50  tff(c_235, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.07/1.50  tff(c_257, plain, (![A_51]: (k3_xboole_0(k1_xboole_0, A_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_235])).
% 3.07/1.50  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.07/1.50  tff(c_266, plain, (![A_51]: (k3_xboole_0(A_51, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_257, c_4])).
% 3.07/1.50  tff(c_22, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.07/1.50  tff(c_485, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.50  tff(c_517, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_485])).
% 3.07/1.50  tff(c_524, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_266, c_517])).
% 3.07/1.50  tff(c_48, plain, (![A_27]: (k2_subset_1(A_27)=A_27)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.07/1.50  tff(c_62, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.07/1.50  tff(c_63, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 3.07/1.50  tff(c_148, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_63])).
% 3.07/1.50  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.07/1.50  tff(c_149, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_54])).
% 3.07/1.50  tff(c_818, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.07/1.50  tff(c_828, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_149, c_818])).
% 3.07/1.50  tff(c_832, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_524, c_828])).
% 3.07/1.50  tff(c_56, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.07/1.50  tff(c_64, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_56])).
% 3.07/1.50  tff(c_228, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_148, c_64])).
% 3.07/1.50  tff(c_833, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_832, c_228])).
% 3.07/1.50  tff(c_836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_833])).
% 3.07/1.50  tff(c_838, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_63])).
% 3.07/1.50  tff(c_52, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.07/1.50  tff(c_1172, plain, (![B_117, A_118]: (r2_hidden(B_117, A_118) | ~m1_subset_1(B_117, A_118) | v1_xboole_0(A_118))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.07/1.50  tff(c_28, plain, (![C_24, A_20]: (r1_tarski(C_24, A_20) | ~r2_hidden(C_24, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.07/1.50  tff(c_1179, plain, (![B_117, A_20]: (r1_tarski(B_117, A_20) | ~m1_subset_1(B_117, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_1172, c_28])).
% 3.07/1.50  tff(c_1184, plain, (![B_119, A_120]: (r1_tarski(B_119, A_120) | ~m1_subset_1(B_119, k1_zfmisc_1(A_120)))), inference(negUnitSimplification, [status(thm)], [c_52, c_1179])).
% 3.07/1.50  tff(c_1197, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1184])).
% 3.07/1.50  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.07/1.50  tff(c_1199, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1197, c_6])).
% 3.07/1.50  tff(c_1205, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_838, c_1199])).
% 3.07/1.50  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.07/1.50  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.07/1.50  tff(c_1061, plain, (![B_109, A_110]: (B_109=A_110 | ~r1_tarski(B_109, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.07/1.50  tff(c_1077, plain, (![A_111]: (k1_xboole_0=A_111 | ~r1_tarski(A_111, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_1061])).
% 3.07/1.50  tff(c_1127, plain, (![B_115]: (k4_xboole_0(k1_xboole_0, B_115)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_1077])).
% 3.07/1.50  tff(c_26, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.07/1.50  tff(c_1132, plain, (![B_115]: (k5_xboole_0(B_115, k1_xboole_0)=k2_xboole_0(B_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1127, c_26])).
% 3.07/1.50  tff(c_1147, plain, (![B_115]: (k5_xboole_0(B_115, k1_xboole_0)=B_115)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1132])).
% 3.07/1.50  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.50  tff(c_915, plain, (![A_94, B_95]: (k3_xboole_0(A_94, B_95)=A_94 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.07/1.50  tff(c_941, plain, (![A_97]: (k3_xboole_0(k1_xboole_0, A_97)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_915])).
% 3.07/1.50  tff(c_950, plain, (![A_97]: (k3_xboole_0(A_97, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_941, c_4])).
% 3.07/1.50  tff(c_1207, plain, (![A_121, B_122]: (k4_xboole_0(A_121, k4_xboole_0(A_121, B_122))=k3_xboole_0(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.50  tff(c_1239, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1207])).
% 3.07/1.50  tff(c_1246, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_950, c_1239])).
% 3.07/1.50  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.07/1.50  tff(c_930, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_915])).
% 3.07/1.50  tff(c_1412, plain, (![A_129, B_130]: (k5_xboole_0(A_129, k3_xboole_0(A_129, B_130))=k4_xboole_0(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.07/1.50  tff(c_1444, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_930, c_1412])).
% 3.07/1.50  tff(c_1457, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1246, c_1444])).
% 3.07/1.50  tff(c_16, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.07/1.50  tff(c_1206, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1197, c_16])).
% 3.07/1.50  tff(c_1428, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1206, c_1412])).
% 3.07/1.50  tff(c_1540, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1457, c_1428])).
% 3.07/1.50  tff(c_1547, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1540, c_26])).
% 3.07/1.50  tff(c_1554, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_2, c_1547])).
% 3.07/1.50  tff(c_1485, plain, (![A_132, B_133]: (k4_xboole_0(A_132, B_133)=k3_subset_1(A_132, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.07/1.50  tff(c_1498, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_1485])).
% 3.07/1.50  tff(c_1505, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1498, c_26])).
% 3.07/1.50  tff(c_1557, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1554, c_1505])).
% 3.07/1.50  tff(c_837, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_63])).
% 3.07/1.50  tff(c_928, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_837, c_915])).
% 3.07/1.50  tff(c_1566, plain, (![A_134, B_135]: (k5_xboole_0(A_134, k3_xboole_0(B_135, A_134))=k4_xboole_0(A_134, B_135))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1412])).
% 3.07/1.50  tff(c_1597, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_928, c_1566])).
% 3.07/1.50  tff(c_1621, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1557, c_1597])).
% 3.07/1.50  tff(c_1670, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1621, c_20])).
% 3.07/1.50  tff(c_1676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1205, c_1670])).
% 3.07/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.50  
% 3.07/1.50  Inference rules
% 3.07/1.50  ----------------------
% 3.07/1.50  #Ref     : 0
% 3.07/1.50  #Sup     : 380
% 3.07/1.50  #Fact    : 0
% 3.07/1.50  #Define  : 0
% 3.07/1.50  #Split   : 2
% 3.07/1.50  #Chain   : 0
% 3.07/1.50  #Close   : 0
% 3.07/1.50  
% 3.07/1.50  Ordering : KBO
% 3.07/1.50  
% 3.07/1.50  Simplification rules
% 3.07/1.50  ----------------------
% 3.07/1.50  #Subsume      : 9
% 3.07/1.50  #Demod        : 179
% 3.07/1.50  #Tautology    : 287
% 3.07/1.50  #SimpNegUnit  : 6
% 3.07/1.50  #BackRed      : 4
% 3.07/1.50  
% 3.07/1.50  #Partial instantiations: 0
% 3.07/1.50  #Strategies tried      : 1
% 3.07/1.50  
% 3.07/1.50  Timing (in seconds)
% 3.07/1.50  ----------------------
% 3.07/1.50  Preprocessing        : 0.31
% 3.07/1.50  Parsing              : 0.16
% 3.07/1.50  CNF conversion       : 0.02
% 3.07/1.50  Main loop            : 0.40
% 3.07/1.50  Inferencing          : 0.14
% 3.07/1.50  Reduction            : 0.14
% 3.07/1.50  Demodulation         : 0.11
% 3.07/1.50  BG Simplification    : 0.02
% 3.07/1.50  Subsumption          : 0.06
% 3.07/1.50  Abstraction          : 0.02
% 3.07/1.50  MUC search           : 0.00
% 3.07/1.50  Cooper               : 0.00
% 3.07/1.50  Total                : 0.75
% 3.07/1.50  Index Insertion      : 0.00
% 3.07/1.50  Index Deletion       : 0.00
% 3.07/1.50  Index Matching       : 0.00
% 3.07/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
