%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:21 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 544 expanded)
%              Number of leaves         :   22 ( 161 expanded)
%              Depth                    :    9
%              Number of atoms          :  245 (1319 expanded)
%              Number of equality atoms :  211 (1247 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1573,plain,(
    ! [A_116,B_117] :
      ( k2_xboole_0(A_116,B_117) = B_117
      | k4_xboole_0(A_116,B_117) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_1601,plain,(
    ! [A_118] : k2_xboole_0(k1_xboole_0,A_118) = A_118 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1573])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(A_7,B_8),B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1607,plain,(
    ! [A_118] : k4_xboole_0(k1_xboole_0,A_118) = k4_xboole_0(A_118,A_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_1601,c_12])).

tff(c_1612,plain,(
    ! [A_118] : k4_xboole_0(A_118,A_118) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1607])).

tff(c_156,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,B_41) = B_41
      | k4_xboole_0(A_40,B_41) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_1133,plain,(
    ! [A_89] : k2_xboole_0(k1_xboole_0,A_89) = A_89 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_1139,plain,(
    ! [A_89] : k4_xboole_0(k1_xboole_0,A_89) = k4_xboole_0(A_89,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_12])).

tff(c_1144,plain,(
    ! [A_89] : k4_xboole_0(A_89,A_89) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1139])).

tff(c_178,plain,(
    ! [A_42] : k2_xboole_0(k1_xboole_0,A_42) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_156])).

tff(c_184,plain,(
    ! [A_42] : k4_xboole_0(k1_xboole_0,A_42) = k4_xboole_0(A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_12])).

tff(c_189,plain,(
    ! [A_42] : k4_xboole_0(A_42,A_42) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_184])).

tff(c_40,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_109,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_142,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_176,plain,(
    k1_tarski('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_247,plain,(
    k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_46,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_317,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_339,plain,(
    ! [B_51,C_52,A_53] :
      ( k2_tarski(B_51,C_52) = A_53
      | k1_tarski(C_52) = A_53
      | k1_tarski(B_51) = A_53
      | k1_xboole_0 = A_53
      | ~ r1_tarski(A_53,k2_tarski(B_51,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_365,plain,(
    ! [B_54,C_55,A_56] :
      ( k2_tarski(B_54,C_55) = A_56
      | k1_tarski(C_55) = A_56
      | k1_tarski(B_54) = A_56
      | k1_xboole_0 = A_56
      | k4_xboole_0(A_56,k2_tarski(B_54,C_55)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_339])).

tff(c_368,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_365])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_142,c_176,c_247,c_368])).

tff(c_391,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_393,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_44,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_272,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_394,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_272])).

tff(c_397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_394])).

tff(c_398,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_400,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_413,plain,(
    ! [A_9] : k4_xboole_0('#skF_1',A_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_400,c_14])).

tff(c_403,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_272])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_403])).

tff(c_472,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_474,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_20,plain,(
    ! [C_12,B_11] : r1_tarski(k1_tarski(C_12),k2_tarski(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_57,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [C_12,B_11] : k4_xboole_0(k1_tarski(C_12),k2_tarski(B_11,C_12)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_484,plain,(
    ! [B_11] : k4_xboole_0('#skF_1',k2_tarski(B_11,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_67])).

tff(c_529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_272])).

tff(c_530,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_26,plain,(
    ! [A_13,B_14] : k4_xboole_0(k1_tarski(A_13),k2_tarski(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_544,plain,(
    ! [B_14] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',B_14)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_26])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_272])).

tff(c_575,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_663,plain,(
    ! [B_69,C_70,A_71] :
      ( k2_tarski(B_69,C_70) = A_71
      | k1_tarski(C_70) = A_71
      | k1_tarski(B_69) = A_71
      | k1_xboole_0 = A_71
      | ~ r1_tarski(A_71,k2_tarski(B_69,C_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_690,plain,(
    ! [B_72,C_73,A_74] :
      ( k2_tarski(B_72,C_73) = A_74
      | k1_tarski(C_73) = A_74
      | k1_tarski(B_72) = A_74
      | k1_xboole_0 = A_74
      | k4_xboole_0(A_74,k2_tarski(B_72,C_73)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_663])).

tff(c_696,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_690])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_142,c_176,c_247,c_696])).

tff(c_721,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_910,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_30])).

tff(c_911,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_910])).

tff(c_926,plain,(
    ! [A_9] : k4_xboole_0('#skF_1',A_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_911,c_14])).

tff(c_720,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_913,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_720])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_913])).

tff(c_1002,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_910])).

tff(c_1004,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1002])).

tff(c_1005,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_720])).

tff(c_1008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_1005])).

tff(c_1009,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1002])).

tff(c_1013,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1009])).

tff(c_1026,plain,(
    ! [B_14] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',B_14)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1013,c_26])).

tff(c_1056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_720])).

tff(c_1057,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1009])).

tff(c_1090,plain,(
    ! [B_87] : r1_tarski('#skF_1',k2_tarski(B_87,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1057,c_20])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1098,plain,(
    ! [B_87] : k4_xboole_0('#skF_1',k2_tarski(B_87,'#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1090,c_10])).

tff(c_1113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_720])).

tff(c_1115,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1326,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_34])).

tff(c_1327,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1326])).

tff(c_1340,plain,(
    ! [A_9] : k4_xboole_0('#skF_1',A_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1327,c_1327,c_14])).

tff(c_1114,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1330,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1327,c_1114])).

tff(c_1399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1340,c_1330])).

tff(c_1400,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1326])).

tff(c_1402,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1400])).

tff(c_1403,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_1114])).

tff(c_1406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_1403])).

tff(c_1407,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1400])).

tff(c_1410,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1407])).

tff(c_1423,plain,(
    ! [B_14] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',B_14)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1410,c_26])).

tff(c_1453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1423,c_1114])).

tff(c_1454,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1407])).

tff(c_1478,plain,(
    ! [B_109] : r1_tarski('#skF_1',k2_tarski(B_109,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1454,c_20])).

tff(c_1486,plain,(
    ! [B_109] : k4_xboole_0('#skF_1',k2_tarski(B_109,'#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1478,c_10])).

tff(c_1512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_1114])).

tff(c_1514,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1745,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1514,c_38])).

tff(c_1746,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1745])).

tff(c_1759,plain,(
    ! [A_9] : k4_xboole_0('#skF_1',A_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1746,c_1746,c_14])).

tff(c_1513,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1752,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1746,c_1513])).

tff(c_1817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_1752])).

tff(c_1818,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1745])).

tff(c_1822,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1818])).

tff(c_1823,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1822,c_1513])).

tff(c_1826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_1823])).

tff(c_1827,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1818])).

tff(c_1829,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1827])).

tff(c_1842,plain,(
    ! [B_14] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',B_14)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1829,c_26])).

tff(c_1872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1842,c_1513])).

tff(c_1873,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1827])).

tff(c_1886,plain,(
    ! [B_11] : k4_xboole_0('#skF_1',k2_tarski(B_11,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1873,c_67])).

tff(c_1981,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1886,c_1513])).

tff(c_1983,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1989,plain,(
    ! [A_9] : k4_xboole_0('#skF_4',A_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_1983,c_14])).

tff(c_105,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_2096,plain,(
    ! [A_157,B_158] :
      ( k2_xboole_0(A_157,B_158) = B_158
      | k4_xboole_0(A_157,B_158) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_105])).

tff(c_2117,plain,(
    ! [A_159] : k2_xboole_0('#skF_4',A_159) = A_159 ),
    inference(superposition,[status(thm),theory(equality)],[c_1989,c_2096])).

tff(c_2123,plain,(
    ! [A_159] : k4_xboole_0(A_159,A_159) = k4_xboole_0('#skF_4',A_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_2117,c_12])).

tff(c_2128,plain,(
    ! [A_159] : k4_xboole_0(A_159,A_159) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1989,c_2123])).

tff(c_42,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2174,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_1983,c_42])).

tff(c_2175,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2174])).

tff(c_1982,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2006,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_1982])).

tff(c_2176,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2175,c_2006])).

tff(c_2179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1989,c_2176])).

tff(c_2180,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2174])).

tff(c_2224,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2180])).

tff(c_2225,plain,(
    k4_xboole_0('#skF_1','#skF_1') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2224,c_2006])).

tff(c_2228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2225])).

tff(c_2229,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2180])).

tff(c_2231,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2229])).

tff(c_1985,plain,(
    ! [A_13,B_14] : k4_xboole_0(k1_tarski(A_13),k2_tarski(A_13,B_14)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_26])).

tff(c_2246,plain,(
    ! [B_14] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',B_14)) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2231,c_1985])).

tff(c_2276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_2006])).

tff(c_2277,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2229])).

tff(c_2041,plain,(
    ! [C_12,B_11] : k4_xboole_0(k1_tarski(C_12),k2_tarski(B_11,C_12)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_67])).

tff(c_2288,plain,(
    ! [B_11] : k4_xboole_0('#skF_1',k2_tarski(B_11,'#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2277,c_2041])).

tff(c_2334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2288,c_2006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.68  
% 3.35/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.68  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.35/1.68  
% 3.35/1.68  %Foreground sorts:
% 3.35/1.68  
% 3.35/1.68  
% 3.35/1.68  %Background operators:
% 3.35/1.68  
% 3.35/1.68  
% 3.35/1.68  %Foreground operators:
% 3.35/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.35/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.35/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.35/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.35/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.35/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.35/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.35/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.35/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.35/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.35/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.35/1.68  
% 3.35/1.70  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.35/1.70  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.35/1.70  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.35/1.70  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.35/1.70  tff(f_74, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 3.35/1.70  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.35/1.70  tff(f_58, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 3.35/1.70  tff(c_14, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.70  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.35/1.70  tff(c_88, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.35/1.70  tff(c_1573, plain, (![A_116, B_117]: (k2_xboole_0(A_116, B_117)=B_117 | k4_xboole_0(A_116, B_117)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_88])).
% 3.35/1.70  tff(c_1601, plain, (![A_118]: (k2_xboole_0(k1_xboole_0, A_118)=A_118)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1573])).
% 3.35/1.70  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.35/1.70  tff(c_1607, plain, (![A_118]: (k4_xboole_0(k1_xboole_0, A_118)=k4_xboole_0(A_118, A_118))), inference(superposition, [status(thm), theory('equality')], [c_1601, c_12])).
% 3.35/1.70  tff(c_1612, plain, (![A_118]: (k4_xboole_0(A_118, A_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1607])).
% 3.35/1.70  tff(c_156, plain, (![A_40, B_41]: (k2_xboole_0(A_40, B_41)=B_41 | k4_xboole_0(A_40, B_41)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_88])).
% 3.35/1.70  tff(c_1133, plain, (![A_89]: (k2_xboole_0(k1_xboole_0, A_89)=A_89)), inference(superposition, [status(thm), theory('equality')], [c_14, c_156])).
% 3.35/1.70  tff(c_1139, plain, (![A_89]: (k4_xboole_0(k1_xboole_0, A_89)=k4_xboole_0(A_89, A_89))), inference(superposition, [status(thm), theory('equality')], [c_1133, c_12])).
% 3.35/1.70  tff(c_1144, plain, (![A_89]: (k4_xboole_0(A_89, A_89)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1139])).
% 3.35/1.70  tff(c_178, plain, (![A_42]: (k2_xboole_0(k1_xboole_0, A_42)=A_42)), inference(superposition, [status(thm), theory('equality')], [c_14, c_156])).
% 3.35/1.70  tff(c_184, plain, (![A_42]: (k4_xboole_0(k1_xboole_0, A_42)=k4_xboole_0(A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_178, c_12])).
% 3.35/1.70  tff(c_189, plain, (![A_42]: (k4_xboole_0(A_42, A_42)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_184])).
% 3.35/1.70  tff(c_40, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.70  tff(c_109, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_40])).
% 3.35/1.70  tff(c_36, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.70  tff(c_142, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_36])).
% 3.35/1.70  tff(c_32, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.70  tff(c_176, plain, (k1_tarski('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_32])).
% 3.35/1.70  tff(c_28, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.70  tff(c_247, plain, (k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_28])).
% 3.35/1.70  tff(c_46, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.70  tff(c_317, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 3.35/1.70  tff(c_339, plain, (![B_51, C_52, A_53]: (k2_tarski(B_51, C_52)=A_53 | k1_tarski(C_52)=A_53 | k1_tarski(B_51)=A_53 | k1_xboole_0=A_53 | ~r1_tarski(A_53, k2_tarski(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.35/1.70  tff(c_365, plain, (![B_54, C_55, A_56]: (k2_tarski(B_54, C_55)=A_56 | k1_tarski(C_55)=A_56 | k1_tarski(B_54)=A_56 | k1_xboole_0=A_56 | k4_xboole_0(A_56, k2_tarski(B_54, C_55))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_339])).
% 3.35/1.70  tff(c_368, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_317, c_365])).
% 3.35/1.70  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_142, c_176, c_247, c_368])).
% 3.35/1.70  tff(c_391, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_46])).
% 3.35/1.70  tff(c_393, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_391])).
% 3.35/1.70  tff(c_44, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.70  tff(c_272, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 3.35/1.70  tff(c_394, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_393, c_272])).
% 3.35/1.70  tff(c_397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_394])).
% 3.35/1.70  tff(c_398, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_391])).
% 3.35/1.70  tff(c_400, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_398])).
% 3.35/1.70  tff(c_413, plain, (![A_9]: (k4_xboole_0('#skF_1', A_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_400, c_14])).
% 3.35/1.70  tff(c_403, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_400, c_272])).
% 3.35/1.70  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_413, c_403])).
% 3.35/1.70  tff(c_472, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_398])).
% 3.35/1.70  tff(c_474, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_472])).
% 3.35/1.70  tff(c_20, plain, (![C_12, B_11]: (r1_tarski(k1_tarski(C_12), k2_tarski(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.35/1.70  tff(c_57, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.35/1.70  tff(c_67, plain, (![C_12, B_11]: (k4_xboole_0(k1_tarski(C_12), k2_tarski(B_11, C_12))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_57])).
% 3.35/1.70  tff(c_484, plain, (![B_11]: (k4_xboole_0('#skF_1', k2_tarski(B_11, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_474, c_67])).
% 3.35/1.70  tff(c_529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_484, c_272])).
% 3.35/1.70  tff(c_530, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_472])).
% 3.35/1.70  tff(c_26, plain, (![A_13, B_14]: (k4_xboole_0(k1_tarski(A_13), k2_tarski(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.35/1.70  tff(c_544, plain, (![B_14]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', B_14))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_530, c_26])).
% 3.35/1.70  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_544, c_272])).
% 3.35/1.70  tff(c_575, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.35/1.70  tff(c_663, plain, (![B_69, C_70, A_71]: (k2_tarski(B_69, C_70)=A_71 | k1_tarski(C_70)=A_71 | k1_tarski(B_69)=A_71 | k1_xboole_0=A_71 | ~r1_tarski(A_71, k2_tarski(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.35/1.70  tff(c_690, plain, (![B_72, C_73, A_74]: (k2_tarski(B_72, C_73)=A_74 | k1_tarski(C_73)=A_74 | k1_tarski(B_72)=A_74 | k1_xboole_0=A_74 | k4_xboole_0(A_74, k2_tarski(B_72, C_73))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_663])).
% 3.35/1.70  tff(c_696, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_575, c_690])).
% 3.35/1.70  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_142, c_176, c_247, c_696])).
% 3.35/1.70  tff(c_721, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 3.35/1.70  tff(c_30, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.70  tff(c_910, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_721, c_30])).
% 3.35/1.70  tff(c_911, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_910])).
% 3.35/1.70  tff(c_926, plain, (![A_9]: (k4_xboole_0('#skF_1', A_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_911, c_911, c_14])).
% 3.35/1.70  tff(c_720, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 3.35/1.70  tff(c_913, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_911, c_720])).
% 3.35/1.70  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_926, c_913])).
% 3.35/1.70  tff(c_1002, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_910])).
% 3.35/1.70  tff(c_1004, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1002])).
% 3.35/1.70  tff(c_1005, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_720])).
% 3.35/1.70  tff(c_1008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_1005])).
% 3.35/1.70  tff(c_1009, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1002])).
% 3.35/1.70  tff(c_1013, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_1009])).
% 3.35/1.70  tff(c_1026, plain, (![B_14]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', B_14))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1013, c_26])).
% 3.35/1.70  tff(c_1056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1026, c_720])).
% 3.35/1.70  tff(c_1057, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1009])).
% 3.35/1.70  tff(c_1090, plain, (![B_87]: (r1_tarski('#skF_1', k2_tarski(B_87, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1057, c_20])).
% 3.35/1.70  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.35/1.70  tff(c_1098, plain, (![B_87]: (k4_xboole_0('#skF_1', k2_tarski(B_87, '#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1090, c_10])).
% 3.35/1.70  tff(c_1113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1098, c_720])).
% 3.35/1.70  tff(c_1115, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 3.35/1.70  tff(c_34, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.70  tff(c_1326, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_34])).
% 3.35/1.70  tff(c_1327, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1326])).
% 3.35/1.70  tff(c_1340, plain, (![A_9]: (k4_xboole_0('#skF_1', A_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1327, c_1327, c_14])).
% 3.35/1.70  tff(c_1114, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.35/1.70  tff(c_1330, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1327, c_1114])).
% 3.35/1.70  tff(c_1399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1340, c_1330])).
% 3.35/1.70  tff(c_1400, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1326])).
% 3.35/1.70  tff(c_1402, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1400])).
% 3.35/1.70  tff(c_1403, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_1114])).
% 3.35/1.70  tff(c_1406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1144, c_1403])).
% 3.35/1.70  tff(c_1407, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1400])).
% 3.35/1.70  tff(c_1410, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_1407])).
% 3.35/1.70  tff(c_1423, plain, (![B_14]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', B_14))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1410, c_26])).
% 3.35/1.70  tff(c_1453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1423, c_1114])).
% 3.35/1.70  tff(c_1454, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1407])).
% 3.35/1.70  tff(c_1478, plain, (![B_109]: (r1_tarski('#skF_1', k2_tarski(B_109, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1454, c_20])).
% 3.35/1.70  tff(c_1486, plain, (![B_109]: (k4_xboole_0('#skF_1', k2_tarski(B_109, '#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1478, c_10])).
% 3.35/1.70  tff(c_1512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1486, c_1114])).
% 3.35/1.70  tff(c_1514, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 3.35/1.70  tff(c_38, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.70  tff(c_1745, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1514, c_38])).
% 3.35/1.70  tff(c_1746, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1745])).
% 3.35/1.70  tff(c_1759, plain, (![A_9]: (k4_xboole_0('#skF_1', A_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1746, c_1746, c_14])).
% 3.35/1.70  tff(c_1513, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.35/1.70  tff(c_1752, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1746, c_1513])).
% 3.35/1.70  tff(c_1817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1759, c_1752])).
% 3.35/1.70  tff(c_1818, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1745])).
% 3.35/1.70  tff(c_1822, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1818])).
% 3.35/1.70  tff(c_1823, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1822, c_1513])).
% 3.35/1.70  tff(c_1826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1612, c_1823])).
% 3.35/1.70  tff(c_1827, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1818])).
% 3.35/1.70  tff(c_1829, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_1827])).
% 3.35/1.70  tff(c_1842, plain, (![B_14]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', B_14))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1829, c_26])).
% 3.35/1.70  tff(c_1872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1842, c_1513])).
% 3.35/1.70  tff(c_1873, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1827])).
% 3.35/1.70  tff(c_1886, plain, (![B_11]: (k4_xboole_0('#skF_1', k2_tarski(B_11, '#skF_3'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1873, c_67])).
% 3.35/1.70  tff(c_1981, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1886, c_1513])).
% 3.35/1.70  tff(c_1983, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 3.35/1.70  tff(c_1989, plain, (![A_9]: (k4_xboole_0('#skF_4', A_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_1983, c_14])).
% 3.35/1.70  tff(c_105, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_88])).
% 3.35/1.70  tff(c_2096, plain, (![A_157, B_158]: (k2_xboole_0(A_157, B_158)=B_158 | k4_xboole_0(A_157, B_158)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_105])).
% 3.35/1.70  tff(c_2117, plain, (![A_159]: (k2_xboole_0('#skF_4', A_159)=A_159)), inference(superposition, [status(thm), theory('equality')], [c_1989, c_2096])).
% 3.35/1.70  tff(c_2123, plain, (![A_159]: (k4_xboole_0(A_159, A_159)=k4_xboole_0('#skF_4', A_159))), inference(superposition, [status(thm), theory('equality')], [c_2117, c_12])).
% 3.35/1.70  tff(c_2128, plain, (![A_159]: (k4_xboole_0(A_159, A_159)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1989, c_2123])).
% 3.35/1.70  tff(c_42, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.70  tff(c_2174, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_1983, c_42])).
% 3.35/1.70  tff(c_2175, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_2174])).
% 3.35/1.70  tff(c_1982, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.35/1.70  tff(c_2006, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_1982])).
% 3.35/1.70  tff(c_2176, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2175, c_2006])).
% 3.35/1.70  tff(c_2179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1989, c_2176])).
% 3.35/1.70  tff(c_2180, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2174])).
% 3.35/1.70  tff(c_2224, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_2180])).
% 3.35/1.70  tff(c_2225, plain, (k4_xboole_0('#skF_1', '#skF_1')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2224, c_2006])).
% 3.35/1.70  tff(c_2228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2225])).
% 3.35/1.70  tff(c_2229, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_2180])).
% 3.35/1.70  tff(c_2231, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_2229])).
% 3.35/1.70  tff(c_1985, plain, (![A_13, B_14]: (k4_xboole_0(k1_tarski(A_13), k2_tarski(A_13, B_14))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_26])).
% 3.35/1.70  tff(c_2246, plain, (![B_14]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', B_14))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2231, c_1985])).
% 3.35/1.70  tff(c_2276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2246, c_2006])).
% 3.35/1.70  tff(c_2277, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2229])).
% 3.35/1.70  tff(c_2041, plain, (![C_12, B_11]: (k4_xboole_0(k1_tarski(C_12), k2_tarski(B_11, C_12))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1983, c_67])).
% 3.35/1.70  tff(c_2288, plain, (![B_11]: (k4_xboole_0('#skF_1', k2_tarski(B_11, '#skF_3'))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2277, c_2041])).
% 3.35/1.70  tff(c_2334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2288, c_2006])).
% 3.35/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.70  
% 3.35/1.70  Inference rules
% 3.35/1.70  ----------------------
% 3.35/1.70  #Ref     : 0
% 3.35/1.70  #Sup     : 519
% 3.35/1.70  #Fact    : 0
% 3.35/1.70  #Define  : 0
% 3.35/1.70  #Split   : 25
% 3.35/1.70  #Chain   : 0
% 3.35/1.70  #Close   : 0
% 3.35/1.70  
% 3.35/1.70  Ordering : KBO
% 3.35/1.70  
% 3.35/1.70  Simplification rules
% 3.35/1.70  ----------------------
% 3.35/1.70  #Subsume      : 28
% 3.35/1.70  #Demod        : 311
% 3.35/1.70  #Tautology    : 381
% 3.35/1.70  #SimpNegUnit  : 14
% 3.35/1.70  #BackRed      : 75
% 3.35/1.70  
% 3.35/1.70  #Partial instantiations: 0
% 3.35/1.70  #Strategies tried      : 1
% 3.35/1.70  
% 3.35/1.70  Timing (in seconds)
% 3.35/1.70  ----------------------
% 3.35/1.70  Preprocessing        : 0.33
% 3.35/1.70  Parsing              : 0.17
% 3.35/1.70  CNF conversion       : 0.02
% 3.35/1.70  Main loop            : 0.54
% 3.35/1.70  Inferencing          : 0.19
% 3.35/1.70  Reduction            : 0.18
% 3.35/1.70  Demodulation         : 0.13
% 3.35/1.70  BG Simplification    : 0.03
% 3.35/1.70  Subsumption          : 0.08
% 3.35/1.71  Abstraction          : 0.03
% 3.35/1.71  MUC search           : 0.00
% 3.35/1.71  Cooper               : 0.00
% 3.35/1.71  Total                : 0.92
% 3.35/1.71  Index Insertion      : 0.00
% 3.35/1.71  Index Deletion       : 0.00
% 3.35/1.71  Index Matching       : 0.00
% 3.35/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
