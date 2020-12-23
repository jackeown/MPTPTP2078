%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:10 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 314 expanded)
%              Number of leaves         :   36 ( 117 expanded)
%              Depth                    :   16
%              Number of atoms          :  119 ( 408 expanded)
%              Number of equality atoms :   73 ( 239 expanded)
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

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

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

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_14,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_223,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_232,plain,(
    ! [A_46] : k3_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_223])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_237,plain,(
    ! [A_46] : k3_xboole_0(A_46,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_4])).

tff(c_10,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_530,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k4_xboole_0(B_76,A_75)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_542,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k2_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_530])).

tff(c_546,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_542])).

tff(c_429,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_438,plain,(
    ! [A_46] : k5_xboole_0(A_46,k1_xboole_0) = k4_xboole_0(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_429])).

tff(c_568,plain,(
    ! [A_78] : k4_xboole_0(A_78,k1_xboole_0) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_438])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_577,plain,(
    ! [A_78] : k4_xboole_0(A_78,A_78) = k3_xboole_0(A_78,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_18])).

tff(c_594,plain,(
    ! [A_78] : k4_xboole_0(A_78,A_78) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_577])).

tff(c_44,plain,(
    ! [A_27] : k2_subset_1(A_27) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_52])).

tff(c_149,plain,(
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

tff(c_306,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_59])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_308,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_50])).

tff(c_599,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,B_80) = k3_subset_1(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_612,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_308,c_599])).

tff(c_727,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_612])).

tff(c_307,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_149])).

tff(c_728,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_727,c_307])).

tff(c_731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_728])).

tff(c_732,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1079,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k4_xboole_0(B_115,A_114)) = k2_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1091,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k2_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1079])).

tff(c_1095,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1091])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_807,plain,(
    ! [A_87,B_88] :
      ( k3_xboole_0(A_87,B_88) = A_87
      | ~ r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_820,plain,(
    ! [A_89] : k3_xboole_0(k1_xboole_0,A_89) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_807])).

tff(c_825,plain,(
    ! [A_89] : k3_xboole_0(A_89,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_4])).

tff(c_1105,plain,(
    ! [A_117,B_118] : k5_xboole_0(A_117,k3_xboole_0(A_117,B_118)) = k4_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1120,plain,(
    ! [A_89] : k5_xboole_0(A_89,k1_xboole_0) = k4_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_1105])).

tff(c_1137,plain,(
    ! [A_119] : k4_xboole_0(A_119,k1_xboole_0) = A_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1120])).

tff(c_1146,plain,(
    ! [A_119] : k4_xboole_0(A_119,A_119) = k3_xboole_0(A_119,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1137,c_18])).

tff(c_1163,plain,(
    ! [A_119] : k4_xboole_0(A_119,A_119) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_1146])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1132,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1105])).

tff(c_1305,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_1132])).

tff(c_48,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1037,plain,(
    ! [B_110,A_111] :
      ( r2_hidden(B_110,A_111)
      | ~ m1_subset_1(B_110,A_111)
      | v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [C_24,A_20] :
      ( r1_tarski(C_24,A_20)
      | ~ r2_hidden(C_24,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1044,plain,(
    ! [B_110,A_20] :
      ( r1_tarski(B_110,A_20)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_1037,c_24])).

tff(c_1049,plain,(
    ! [B_112,A_113] :
      ( r1_tarski(B_112,A_113)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_113)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1044])).

tff(c_1062,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1049])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1066,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1062,c_12])).

tff(c_1114,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1066,c_1105])).

tff(c_1349,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1114])).

tff(c_22,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1353,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_22])).

tff(c_1362,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_2,c_1353])).

tff(c_1168,plain,(
    ! [A_120,B_121] :
      ( k4_xboole_0(A_120,B_121) = k3_subset_1(A_120,B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1181,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1168])).

tff(c_1290,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1181,c_22])).

tff(c_1517,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1362,c_1290])).

tff(c_733,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_817,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_733,c_807])).

tff(c_950,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_817,c_4])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2402,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_8])).

tff(c_2417,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1517,c_2402])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1440,plain,(
    ! [A_130,B_131] : k3_xboole_0(k4_xboole_0(A_130,B_131),A_130) = k4_xboole_0(A_130,B_131) ),
    inference(resolution,[status(thm)],[c_16,c_807])).

tff(c_1498,plain,(
    ! [A_3,B_131] : k3_xboole_0(A_3,k4_xboole_0(A_3,B_131)) = k4_xboole_0(A_3,B_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1440])).

tff(c_2424,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2417,c_1498])).

tff(c_2448,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2417,c_1066,c_2424])).

tff(c_2450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_732,c_2448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.62  
% 3.27/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.62  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.27/1.62  
% 3.27/1.62  %Foreground sorts:
% 3.27/1.62  
% 3.27/1.62  
% 3.27/1.62  %Background operators:
% 3.27/1.62  
% 3.27/1.62  
% 3.27/1.62  %Foreground operators:
% 3.27/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.27/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.27/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.27/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.27/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.27/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.27/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.27/1.62  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.27/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.27/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.62  
% 3.65/1.64  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.65/1.64  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.65/1.64  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.65/1.64  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.65/1.64  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.65/1.64  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.65/1.64  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.65/1.64  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.65/1.64  tff(f_71, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.65/1.64  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 3.65/1.64  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.65/1.64  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.65/1.64  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.65/1.64  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.65/1.64  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.65/1.64  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.65/1.64  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.65/1.64  tff(c_14, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.65/1.64  tff(c_223, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.65/1.64  tff(c_232, plain, (![A_46]: (k3_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_223])).
% 3.65/1.64  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.65/1.64  tff(c_237, plain, (![A_46]: (k3_xboole_0(A_46, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_232, c_4])).
% 3.65/1.64  tff(c_10, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.65/1.64  tff(c_20, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.65/1.64  tff(c_530, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k4_xboole_0(B_76, A_75))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.65/1.64  tff(c_542, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k2_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_530])).
% 3.65/1.64  tff(c_546, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_542])).
% 3.65/1.64  tff(c_429, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.65/1.64  tff(c_438, plain, (![A_46]: (k5_xboole_0(A_46, k1_xboole_0)=k4_xboole_0(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_237, c_429])).
% 3.65/1.64  tff(c_568, plain, (![A_78]: (k4_xboole_0(A_78, k1_xboole_0)=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_546, c_438])).
% 3.65/1.64  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.65/1.64  tff(c_577, plain, (![A_78]: (k4_xboole_0(A_78, A_78)=k3_xboole_0(A_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_568, c_18])).
% 3.65/1.64  tff(c_594, plain, (![A_78]: (k4_xboole_0(A_78, A_78)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_237, c_577])).
% 3.65/1.64  tff(c_44, plain, (![A_27]: (k2_subset_1(A_27)=A_27)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.65/1.64  tff(c_52, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.65/1.64  tff(c_60, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_52])).
% 3.65/1.64  tff(c_149, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 3.65/1.64  tff(c_58, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.65/1.64  tff(c_59, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_58])).
% 3.65/1.64  tff(c_306, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_149, c_59])).
% 3.65/1.64  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.65/1.64  tff(c_308, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_50])).
% 3.65/1.64  tff(c_599, plain, (![A_79, B_80]: (k4_xboole_0(A_79, B_80)=k3_subset_1(A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.65/1.64  tff(c_612, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_308, c_599])).
% 3.65/1.64  tff(c_727, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_594, c_612])).
% 3.65/1.64  tff(c_307, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_306, c_149])).
% 3.65/1.64  tff(c_728, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_727, c_307])).
% 3.65/1.64  tff(c_731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_728])).
% 3.65/1.64  tff(c_732, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 3.65/1.64  tff(c_1079, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k4_xboole_0(B_115, A_114))=k2_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.65/1.64  tff(c_1091, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k2_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1079])).
% 3.65/1.64  tff(c_1095, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1091])).
% 3.65/1.64  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.65/1.64  tff(c_807, plain, (![A_87, B_88]: (k3_xboole_0(A_87, B_88)=A_87 | ~r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.65/1.64  tff(c_820, plain, (![A_89]: (k3_xboole_0(k1_xboole_0, A_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_807])).
% 3.65/1.64  tff(c_825, plain, (![A_89]: (k3_xboole_0(A_89, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_820, c_4])).
% 3.65/1.64  tff(c_1105, plain, (![A_117, B_118]: (k5_xboole_0(A_117, k3_xboole_0(A_117, B_118))=k4_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.65/1.64  tff(c_1120, plain, (![A_89]: (k5_xboole_0(A_89, k1_xboole_0)=k4_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_825, c_1105])).
% 3.65/1.64  tff(c_1137, plain, (![A_119]: (k4_xboole_0(A_119, k1_xboole_0)=A_119)), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1120])).
% 3.65/1.64  tff(c_1146, plain, (![A_119]: (k4_xboole_0(A_119, A_119)=k3_xboole_0(A_119, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1137, c_18])).
% 3.65/1.64  tff(c_1163, plain, (![A_119]: (k4_xboole_0(A_119, A_119)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_825, c_1146])).
% 3.65/1.64  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.65/1.64  tff(c_1132, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1105])).
% 3.65/1.64  tff(c_1305, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_1132])).
% 3.65/1.64  tff(c_48, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.65/1.64  tff(c_1037, plain, (![B_110, A_111]: (r2_hidden(B_110, A_111) | ~m1_subset_1(B_110, A_111) | v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.65/1.64  tff(c_24, plain, (![C_24, A_20]: (r1_tarski(C_24, A_20) | ~r2_hidden(C_24, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.65/1.64  tff(c_1044, plain, (![B_110, A_20]: (r1_tarski(B_110, A_20) | ~m1_subset_1(B_110, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_1037, c_24])).
% 3.65/1.64  tff(c_1049, plain, (![B_112, A_113]: (r1_tarski(B_112, A_113) | ~m1_subset_1(B_112, k1_zfmisc_1(A_113)))), inference(negUnitSimplification, [status(thm)], [c_48, c_1044])).
% 3.65/1.64  tff(c_1062, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1049])).
% 3.65/1.64  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.65/1.64  tff(c_1066, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1062, c_12])).
% 3.65/1.64  tff(c_1114, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1066, c_1105])).
% 3.65/1.64  tff(c_1349, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1114])).
% 3.65/1.64  tff(c_22, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.65/1.64  tff(c_1353, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1349, c_22])).
% 3.65/1.64  tff(c_1362, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_2, c_1353])).
% 3.65/1.64  tff(c_1168, plain, (![A_120, B_121]: (k4_xboole_0(A_120, B_121)=k3_subset_1(A_120, B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(A_120)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.65/1.64  tff(c_1181, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1168])).
% 3.65/1.64  tff(c_1290, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1181, c_22])).
% 3.65/1.64  tff(c_1517, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1362, c_1290])).
% 3.65/1.64  tff(c_733, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 3.65/1.64  tff(c_817, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_733, c_807])).
% 3.65/1.64  tff(c_950, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_817, c_4])).
% 3.65/1.64  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.65/1.64  tff(c_2402, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_950, c_8])).
% 3.65/1.64  tff(c_2417, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1517, c_2402])).
% 3.65/1.64  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.65/1.64  tff(c_1440, plain, (![A_130, B_131]: (k3_xboole_0(k4_xboole_0(A_130, B_131), A_130)=k4_xboole_0(A_130, B_131))), inference(resolution, [status(thm)], [c_16, c_807])).
% 3.65/1.64  tff(c_1498, plain, (![A_3, B_131]: (k3_xboole_0(A_3, k4_xboole_0(A_3, B_131))=k4_xboole_0(A_3, B_131))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1440])).
% 3.65/1.64  tff(c_2424, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2417, c_1498])).
% 3.65/1.64  tff(c_2448, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2417, c_1066, c_2424])).
% 3.65/1.64  tff(c_2450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_732, c_2448])).
% 3.65/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.64  
% 3.65/1.64  Inference rules
% 3.65/1.64  ----------------------
% 3.65/1.64  #Ref     : 0
% 3.65/1.64  #Sup     : 581
% 3.65/1.64  #Fact    : 0
% 3.65/1.64  #Define  : 0
% 3.65/1.64  #Split   : 1
% 3.65/1.64  #Chain   : 0
% 3.65/1.64  #Close   : 0
% 3.65/1.64  
% 3.65/1.64  Ordering : KBO
% 3.65/1.64  
% 3.65/1.64  Simplification rules
% 3.65/1.64  ----------------------
% 3.65/1.64  #Subsume      : 8
% 3.65/1.64  #Demod        : 407
% 3.65/1.64  #Tautology    : 461
% 3.65/1.64  #SimpNegUnit  : 7
% 3.65/1.64  #BackRed      : 5
% 3.65/1.64  
% 3.65/1.64  #Partial instantiations: 0
% 3.65/1.64  #Strategies tried      : 1
% 3.65/1.64  
% 3.65/1.64  Timing (in seconds)
% 3.65/1.64  ----------------------
% 3.65/1.64  Preprocessing        : 0.34
% 3.65/1.64  Parsing              : 0.17
% 3.65/1.64  CNF conversion       : 0.02
% 3.65/1.64  Main loop            : 0.53
% 3.65/1.64  Inferencing          : 0.19
% 3.65/1.64  Reduction            : 0.21
% 3.65/1.64  Demodulation         : 0.16
% 3.65/1.64  BG Simplification    : 0.02
% 3.65/1.64  Subsumption          : 0.07
% 3.65/1.64  Abstraction          : 0.03
% 3.65/1.64  MUC search           : 0.00
% 3.65/1.64  Cooper               : 0.00
% 3.65/1.64  Total                : 0.91
% 3.65/1.64  Index Insertion      : 0.00
% 3.65/1.64  Index Deletion       : 0.00
% 3.65/1.64  Index Matching       : 0.00
% 3.65/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
