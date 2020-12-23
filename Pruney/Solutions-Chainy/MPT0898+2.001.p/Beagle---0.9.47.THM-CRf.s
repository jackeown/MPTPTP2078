%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:49 EST 2020

% Result     : Theorem 13.11s
% Output     : CNFRefutation 13.11s
% Verified   : 
% Statistics : Number of formulae       :  230 (1605 expanded)
%              Number of leaves         :   19 ( 516 expanded)
%              Depth                    :   17
%              Number of atoms          :  399 (3502 expanded)
%              Number of equality atoms :  195 (1851 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_40,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_393,plain,(
    ! [A_74,B_75,C_76,D_77] : k2_zfmisc_1(k3_zfmisc_1(A_74,B_75,C_76),D_77) = k4_zfmisc_1(A_74,B_75,C_76,D_77) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(k2_zfmisc_1(A_8,C_10),k2_zfmisc_1(B_9,C_10))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30926,plain,(
    ! [C_5081,B_5084,B_5082,A_5083,D_5080] :
      ( r1_tarski(k4_zfmisc_1(A_5083,B_5084,C_5081,D_5080),k2_zfmisc_1(B_5082,D_5080))
      | ~ r1_tarski(k3_zfmisc_1(A_5083,B_5084,C_5081),B_5082) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_20])).

tff(c_31229,plain,(
    ! [B_5092] :
      ( r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),k2_zfmisc_1(B_5092,'#skF_2'))
      | ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),B_5092) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_30926])).

tff(c_31251,plain,
    ( r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),k1_xboole_0)
    | ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_31229])).

tff(c_32992,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_31251])).

tff(c_680,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k4_zfmisc_1(A_100,B_101,C_102,D_103) != k1_xboole_0
      | k1_xboole_0 = D_103
      | k1_xboole_0 = C_102
      | k1_xboole_0 = B_101
      | k1_xboole_0 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_683,plain,
    ( k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_680])).

tff(c_953,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_683])).

tff(c_9596,plain,(
    ! [C_435,A_433,D_434,A_436,B_437] :
      ( r1_tarski(k2_zfmisc_1(A_433,D_434),k4_zfmisc_1(A_436,B_437,C_435,D_434))
      | ~ r1_tarski(A_433,k3_zfmisc_1(A_436,B_437,C_435)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_20])).

tff(c_10325,plain,(
    ! [A_448] :
      ( r1_tarski(k2_zfmisc_1(A_448,'#skF_2'),k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'))
      | ~ r1_tarski(A_448,k3_zfmisc_1('#skF_2','#skF_2','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_9596])).

tff(c_10355,plain,
    ( r1_tarski(k1_xboole_0,k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'))
    | ~ r1_tarski(k1_xboole_0,k3_zfmisc_1('#skF_2','#skF_2','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_10325])).

tff(c_10471,plain,(
    ~ r1_tarski(k1_xboole_0,k3_zfmisc_1('#skF_2','#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_10355])).

tff(c_10747,plain,(
    ! [B_462,D_458,A_461,C_459,B_460] :
      ( r1_tarski(k4_zfmisc_1(A_461,B_462,C_459,D_458),k2_zfmisc_1(B_460,D_458))
      | ~ r1_tarski(k3_zfmisc_1(A_461,B_462,C_459),B_460) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_20])).

tff(c_10855,plain,(
    ! [B_463] :
      ( r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),k2_zfmisc_1(B_463,'#skF_2'))
      | ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),B_463) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_10747])).

tff(c_10885,plain,
    ( r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),k1_xboole_0)
    | ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_10855])).

tff(c_11014,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_10885])).

tff(c_420,plain,(
    ! [A_74,A_8,D_77,B_75,C_76] :
      ( r1_tarski(k2_zfmisc_1(A_8,D_77),k4_zfmisc_1(A_74,B_75,C_76,D_77))
      | ~ r1_tarski(A_8,k3_zfmisc_1(A_74,B_75,C_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_20])).

tff(c_28,plain,(
    ! [A_18,B_19,C_20,D_21] : k2_zfmisc_1(k3_zfmisc_1(A_18,B_19,C_20),D_21) = k4_zfmisc_1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1129,plain,(
    ! [B_131,D_132,A_133,C_134] :
      ( r1_tarski(B_131,D_132)
      | k2_zfmisc_1(A_133,B_131) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_133,B_131),k2_zfmisc_1(C_134,D_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12188,plain,(
    ! [C_502,B_504,D_503,A_501,B_499,A_500] :
      ( r1_tarski(B_499,D_503)
      | k2_zfmisc_1(A_500,B_499) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_500,B_499),k4_zfmisc_1(A_501,B_504,C_502,D_503)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1129])).

tff(c_12927,plain,(
    ! [B_516,A_517] :
      ( r1_tarski(B_516,'#skF_2')
      | k2_zfmisc_1(A_517,B_516) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_517,B_516),k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_12188])).

tff(c_12988,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_1','#skF_2')
      | k2_zfmisc_1(A_8,'#skF_1') = k1_xboole_0
      | ~ r1_tarski(A_8,k3_zfmisc_1('#skF_1','#skF_1','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_420,c_12927])).

tff(c_14612,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_12988])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14614,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_14612,c_2])).

tff(c_14617,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_14614])).

tff(c_9670,plain,(
    ! [A_433] :
      ( r1_tarski(k2_zfmisc_1(A_433,'#skF_2'),k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'))
      | ~ r1_tarski(A_433,k3_zfmisc_1('#skF_2','#skF_2','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_9596])).

tff(c_12294,plain,(
    ! [A_433] :
      ( r1_tarski('#skF_2','#skF_1')
      | k2_zfmisc_1(A_433,'#skF_2') = k1_xboole_0
      | ~ r1_tarski(A_433,k3_zfmisc_1('#skF_2','#skF_2','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_9670,c_12188])).

tff(c_14851,plain,(
    ! [A_551] :
      ( k2_zfmisc_1(A_551,'#skF_2') = k1_xboole_0
      | ~ r1_tarski(A_551,k3_zfmisc_1('#skF_2','#skF_2','#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14617,c_12294])).

tff(c_14910,plain,(
    k2_zfmisc_1(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_14851])).

tff(c_456,plain,(
    ! [B_78,A_79,C_80] :
      ( ~ r1_tarski(k2_zfmisc_1(B_78,A_79),k2_zfmisc_1(C_80,A_79))
      | r1_tarski(B_78,C_80)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_487,plain,(
    ! [B_78,B_4] :
      ( ~ r1_tarski(k2_zfmisc_1(B_78,B_4),k1_xboole_0)
      | r1_tarski(B_78,k1_xboole_0)
      | k1_xboole_0 = B_4 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_456])).

tff(c_15080,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),k1_xboole_0)
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_14910,c_487])).

tff(c_15202,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),k1_xboole_0)
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15080])).

tff(c_15203,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_11014,c_15202])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_301,plain,(
    ! [C_61,A_62,B_63] :
      ( r1_tarski(k2_zfmisc_1(C_61,A_62),k2_zfmisc_1(C_61,B_63))
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_312,plain,(
    ! [A_3,B_63] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_3,B_63))
      | ~ r1_tarski(k1_xboole_0,B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_301])).

tff(c_1703,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( r1_tarski(k1_xboole_0,k4_zfmisc_1(A_160,B_161,C_162,D_163))
      | ~ r1_tarski(k1_xboole_0,D_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_312])).

tff(c_1723,plain,
    ( r1_tarski(k1_xboole_0,k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'))
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1703])).

tff(c_1768,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1723])).

tff(c_15312,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15203,c_1768])).

tff(c_15364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15312])).

tff(c_15367,plain,(
    ! [A_552] :
      ( k2_zfmisc_1(A_552,'#skF_1') = k1_xboole_0
      | ~ r1_tarski(A_552,k3_zfmisc_1('#skF_1','#skF_1','#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_12988])).

tff(c_15426,plain,(
    k2_zfmisc_1(k3_zfmisc_1('#skF_1','#skF_1','#skF_1'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_15367])).

tff(c_15614,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15426,c_28])).

tff(c_15714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_953,c_15614])).

tff(c_15716,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_10885])).

tff(c_244,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(k2_zfmisc_1(A_54,C_55),k2_zfmisc_1(B_56,C_55))
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_264,plain,(
    ! [A_54,B_4] :
      ( r1_tarski(k2_zfmisc_1(A_54,B_4),k1_xboole_0)
      | ~ r1_tarski(A_54,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_244])).

tff(c_315,plain,(
    ! [A_3,A_62] :
      ( r1_tarski(k2_zfmisc_1(A_3,A_62),k1_xboole_0)
      | ~ r1_tarski(A_62,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_301])).

tff(c_954,plain,(
    ! [B_114,B_115] :
      ( ~ r1_tarski(k2_zfmisc_1(B_114,B_115),k1_xboole_0)
      | r1_tarski(B_114,k1_xboole_0)
      | k1_xboole_0 = B_115 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_456])).

tff(c_983,plain,(
    ! [A_3,A_62] :
      ( r1_tarski(A_3,k1_xboole_0)
      | k1_xboole_0 = A_62
      | ~ r1_tarski(A_62,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_315,c_954])).

tff(c_991,plain,(
    ! [A_116] :
      ( k1_xboole_0 = A_116
      | ~ r1_tarski(A_116,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_983])).

tff(c_1010,plain,(
    ! [A_117,A_118] :
      ( k2_zfmisc_1(A_117,A_118) = k1_xboole_0
      | ~ r1_tarski(A_118,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_315,c_991])).

tff(c_1022,plain,(
    ! [A_117,A_54,B_4] :
      ( k2_zfmisc_1(A_117,k2_zfmisc_1(A_54,B_4)) = k1_xboole_0
      | ~ r1_tarski(A_54,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_264,c_1010])).

tff(c_550,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_tarski(k2_zfmisc_1(A_84,B_85),k2_zfmisc_1(A_84,C_86))
      | r1_tarski(B_85,C_86)
      | k1_xboole_0 = A_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1547,plain,(
    ! [A_148,C_149] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_148,C_149))
      | r1_tarski(k1_xboole_0,C_149)
      | k1_xboole_0 = A_148 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_550])).

tff(c_1553,plain,(
    ! [A_54,B_4,A_117] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | r1_tarski(k1_xboole_0,k2_zfmisc_1(A_54,B_4))
      | k1_xboole_0 = A_117
      | ~ r1_tarski(A_54,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1022,c_1547])).

tff(c_1581,plain,(
    ! [A_54,B_4,A_117] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_54,B_4))
      | k1_xboole_0 = A_117
      | ~ r1_tarski(A_54,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1553])).

tff(c_3649,plain,(
    ! [A_231,B_232] :
      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(A_231,B_232))
      | ~ r1_tarski(A_231,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_1581])).

tff(c_484,plain,(
    ! [C_80,B_4] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(C_80,B_4))
      | r1_tarski(k1_xboole_0,C_80)
      | k1_xboole_0 = B_4 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_456])).

tff(c_3719,plain,(
    ! [A_231,B_232] :
      ( r1_tarski(k1_xboole_0,A_231)
      | k1_xboole_0 = B_232
      | ~ r1_tarski(A_231,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3649,c_484])).

tff(c_3730,plain,(
    ! [A_231] :
      ( r1_tarski(k1_xboole_0,A_231)
      | ~ r1_tarski(A_231,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_3719])).

tff(c_15849,plain,(
    r1_tarski(k1_xboole_0,k3_zfmisc_1('#skF_2','#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_15716,c_3730])).

tff(c_15874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10471,c_15849])).

tff(c_15876,plain,(
    r1_tarski(k1_xboole_0,k3_zfmisc_1('#skF_2','#skF_2','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_10355])).

tff(c_504,plain,(
    ! [C_81,B_82] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(C_81,B_82))
      | r1_tarski(k1_xboole_0,C_81)
      | k1_xboole_0 = B_82 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_456])).

tff(c_523,plain,(
    ! [A_3,B_63] :
      ( r1_tarski(k1_xboole_0,A_3)
      | k1_xboole_0 = B_63
      | ~ r1_tarski(k1_xboole_0,B_63) ) ),
    inference(resolution,[status(thm)],[c_312,c_504])).

tff(c_530,plain,(
    ! [B_63] :
      ( k1_xboole_0 = B_63
      | ~ r1_tarski(k1_xboole_0,B_63) ) ),
    inference(splitLeft,[status(thm)],[c_523])).

tff(c_15912,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15876,c_530])).

tff(c_165,plain,(
    ! [A_45,B_46,C_47] : k2_zfmisc_1(k2_zfmisc_1(A_45,B_46),C_47) = k3_zfmisc_1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_174,plain,(
    ! [C_47,A_45,B_46] :
      ( k1_xboole_0 = C_47
      | k2_zfmisc_1(A_45,B_46) = k1_xboole_0
      | k3_zfmisc_1(A_45,B_46,C_47) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_8])).

tff(c_16002,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15912,c_174])).

tff(c_16042,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_16002])).

tff(c_16287,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_16042,c_8])).

tff(c_16354,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16287,c_1768])).

tff(c_16406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16354])).

tff(c_16407,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16002])).

tff(c_16473,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16407,c_1768])).

tff(c_16525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16473])).

tff(c_16527,plain,(
    ! [B_557] : k1_xboole_0 = B_557 ),
    inference(splitRight,[status(thm)],[c_3719])).

tff(c_16676,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_16527,c_953])).

tff(c_16834,plain,(
    ! [A_834] : k1_xboole_0 = A_834 ),
    inference(splitRight,[status(thm)],[c_1581])).

tff(c_16974,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_16834,c_953])).

tff(c_16976,plain,(
    r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1723])).

tff(c_17003,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16976,c_530])).

tff(c_1639,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( r1_tarski(k4_zfmisc_1(A_152,B_153,C_154,D_155),k1_xboole_0)
      | ~ r1_tarski(D_155,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_315])).

tff(c_1659,plain,
    ( r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),k1_xboole_0)
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1639])).

tff(c_1749,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1659])).

tff(c_17007,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17003,c_1749])).

tff(c_17058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_17007])).

tff(c_17060,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1659])).

tff(c_990,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ r1_tarski(A_62,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_983])).

tff(c_17171,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_17060,c_990])).

tff(c_17191,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17171,c_953])).

tff(c_34,plain,(
    ! [A_22,B_23,D_25] : k4_zfmisc_1(A_22,B_23,k1_xboole_0,D_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_17217,plain,(
    ! [A_22,B_23,D_25] : k4_zfmisc_1(A_22,B_23,'#skF_2',D_25) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17171,c_17171,c_34])).

tff(c_17442,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17217,c_42])).

tff(c_17450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17191,c_17442])).

tff(c_17451,plain,(
    ! [A_3] : r1_tarski(A_3,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_983])).

tff(c_17609,plain,(
    ! [A_1109,C_1110,B_1111,D_1112] :
      ( r1_tarski(A_1109,C_1110)
      | k2_zfmisc_1(A_1109,B_1111) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_1109,B_1111),k2_zfmisc_1(C_1110,D_1112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_17645,plain,(
    ! [A_1109,A_3,B_1111] :
      ( r1_tarski(A_1109,A_3)
      | k2_zfmisc_1(A_1109,B_1111) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_1109,B_1111),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_17609])).

tff(c_17673,plain,(
    ! [A_1113,A_1114,B_1115] :
      ( r1_tarski(A_1113,A_1114)
      | k2_zfmisc_1(A_1113,B_1115) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17451,c_17645])).

tff(c_17846,plain,(
    ! [B_1115,A_1113,A_1114] :
      ( k1_xboole_0 = B_1115
      | k1_xboole_0 = A_1113
      | r1_tarski(A_1113,A_1114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17673,c_8])).

tff(c_17852,plain,(
    ! [A_1113,A_1114] :
      ( k1_xboole_0 = A_1113
      | r1_tarski(A_1113,A_1114) ) ),
    inference(splitLeft,[status(thm)],[c_17846])).

tff(c_17853,plain,(
    ! [A_1116,A_1117] :
      ( k1_xboole_0 = A_1116
      | r1_tarski(A_1116,A_1117) ) ),
    inference(splitLeft,[status(thm)],[c_17846])).

tff(c_17925,plain,(
    ! [A_1119,A_1118] :
      ( A_1119 = A_1118
      | ~ r1_tarski(A_1118,A_1119)
      | k1_xboole_0 = A_1119 ) ),
    inference(resolution,[status(thm)],[c_17853,c_2])).

tff(c_18078,plain,(
    ! [A_1121,A_1120] :
      ( A_1121 = A_1120
      | k1_xboole_0 = A_1120
      | k1_xboole_0 = A_1121 ) ),
    inference(resolution,[status(thm)],[c_17852,c_17925])).

tff(c_17538,plain,(
    ! [A_1101,B_1102,C_1103,D_1104] :
      ( r1_tarski(k1_xboole_0,k4_zfmisc_1(A_1101,B_1102,C_1103,D_1104))
      | ~ r1_tarski(k1_xboole_0,D_1104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_312])).

tff(c_17558,plain,
    ( r1_tarski(k1_xboole_0,k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'))
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_17538])).

tff(c_17914,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_17558])).

tff(c_20991,plain,(
    ! [A_2742,A_2743] :
      ( ~ r1_tarski(A_2742,'#skF_2')
      | A_2743 = A_2742
      | k1_xboole_0 = A_2743 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18078,c_17914])).

tff(c_21082,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_20991])).

tff(c_21083,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,'#skF_1')
      | '#skF_2' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21082,c_17451])).

tff(c_21586,plain,(
    ! [A_3289] : r1_tarski(A_3289,'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_21083])).

tff(c_21637,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_21586,c_530])).

tff(c_21283,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_20991])).

tff(c_21284,plain,(
    ! [A_22,B_23,D_25] :
      ( k4_zfmisc_1(A_22,B_23,'#skF_1',D_25) = k1_xboole_0
      | '#skF_2' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21283,c_34])).

tff(c_21427,plain,(
    ! [A_22,B_23,D_25] : k4_zfmisc_1(A_22,B_23,'#skF_1',D_25) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_21284])).

tff(c_21998,plain,(
    ! [A_22,B_23,D_25] : k4_zfmisc_1(A_22,B_23,'#skF_1',D_25) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21637,c_21427])).

tff(c_21028,plain,(
    ! [A_2780] :
      ( A_2780 = '#skF_2'
      | k1_xboole_0 = A_2780 ) ),
    inference(resolution,[status(thm)],[c_6,c_20991])).

tff(c_21380,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_21028,c_953])).

tff(c_24348,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21998,c_21380])).

tff(c_24349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_24348])).

tff(c_24350,plain,(
    r1_tarski(k1_xboole_0,k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_17558])).

tff(c_24398,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24350,c_530])).

tff(c_24411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_953,c_24398])).

tff(c_24413,plain,(
    ! [B_4642] : k1_xboole_0 = B_4642 ),
    inference(splitRight,[status(thm)],[c_17846])).

tff(c_24486,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_24413,c_953])).

tff(c_24488,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_30,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( k4_zfmisc_1(A_22,B_23,C_24,D_25) != k1_xboole_0
      | k1_xboole_0 = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24496,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_24488,c_30])).

tff(c_24487,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_24813,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24496,c_24496,c_24496,c_24496,c_24487])).

tff(c_24814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_40,c_40,c_24813])).

tff(c_24815,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(splitRight,[status(thm)],[c_523])).

tff(c_25432,plain,(
    ! [A_4853,B_4854,C_4855,D_4856] :
      ( k4_zfmisc_1(A_4853,B_4854,C_4855,D_4856) != k1_xboole_0
      | k1_xboole_0 = D_4856
      | k1_xboole_0 = C_4855
      | k1_xboole_0 = B_4854
      | k1_xboole_0 = A_4853 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_25435,plain,
    ( k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_25432])).

tff(c_25886,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_25435])).

tff(c_31777,plain,(
    ! [B_5107,A_5103,C_5105,A_5106,D_5104] :
      ( r1_tarski(k2_zfmisc_1(A_5103,D_5104),k4_zfmisc_1(A_5106,B_5107,C_5105,D_5104))
      | ~ r1_tarski(A_5103,k3_zfmisc_1(A_5106,B_5107,C_5105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_20])).

tff(c_31842,plain,(
    ! [A_5103] :
      ( r1_tarski(k2_zfmisc_1(A_5103,'#skF_2'),k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'))
      | ~ r1_tarski(A_5103,k3_zfmisc_1('#skF_2','#skF_2','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_31777])).

tff(c_25112,plain,(
    ! [B_4834,D_4835,A_4836,C_4837] :
      ( r1_tarski(B_4834,D_4835)
      | k2_zfmisc_1(A_4836,B_4834) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_4836,B_4834),k2_zfmisc_1(C_4837,D_4835)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34711,plain,(
    ! [A_5184,B_5183,D_5186,A_5182,B_5187,C_5185] :
      ( r1_tarski(B_5183,D_5186)
      | k2_zfmisc_1(A_5182,B_5183) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_5182,B_5183),k4_zfmisc_1(A_5184,B_5187,C_5185,D_5186)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_25112])).

tff(c_34823,plain,(
    ! [A_5103] :
      ( r1_tarski('#skF_2','#skF_1')
      | k2_zfmisc_1(A_5103,'#skF_2') = k1_xboole_0
      | ~ r1_tarski(A_5103,k3_zfmisc_1('#skF_2','#skF_2','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_31842,c_34711])).

tff(c_35920,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34823])).

tff(c_35922,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_35920,c_2])).

tff(c_35925,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_35922])).

tff(c_34852,plain,(
    ! [B_5188,A_5189] :
      ( r1_tarski(B_5188,'#skF_2')
      | k2_zfmisc_1(A_5189,B_5188) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_5189,B_5188),k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_34711])).

tff(c_34919,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_1','#skF_2')
      | k2_zfmisc_1(A_8,'#skF_1') = k1_xboole_0
      | ~ r1_tarski(A_8,k3_zfmisc_1('#skF_1','#skF_1','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_420,c_34852])).

tff(c_37015,plain,(
    ! [A_5224] :
      ( k2_zfmisc_1(A_5224,'#skF_1') = k1_xboole_0
      | ~ r1_tarski(A_5224,k3_zfmisc_1('#skF_1','#skF_1','#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_35925,c_34919])).

tff(c_37096,plain,(
    k2_zfmisc_1(k3_zfmisc_1('#skF_1','#skF_1','#skF_1'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_37015])).

tff(c_34800,plain,(
    ! [B_5183,A_5182] :
      ( r1_tarski(B_5183,'#skF_2')
      | k2_zfmisc_1(A_5182,B_5183) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_5182,B_5183),k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_34711])).

tff(c_37124,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | k2_zfmisc_1(k3_zfmisc_1('#skF_1','#skF_1','#skF_1'),'#skF_1') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37096,c_34800])).

tff(c_37277,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24815,c_28,c_37124])).

tff(c_37279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25886,c_35925,c_37277])).

tff(c_37282,plain,(
    ! [A_5225] :
      ( k2_zfmisc_1(A_5225,'#skF_2') = k1_xboole_0
      | ~ r1_tarski(A_5225,k3_zfmisc_1('#skF_2','#skF_2','#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_34823])).

tff(c_37351,plain,(
    k2_zfmisc_1(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_37282])).

tff(c_37463,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),k1_xboole_0)
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_37351,c_487])).

tff(c_37561,plain,
    ( r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),k1_xboole_0)
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24815,c_37463])).

tff(c_37562,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32992,c_37561])).

tff(c_25384,plain,(
    ! [A_4849,B_4850,C_4851,D_4852] :
      ( r1_tarski(k4_zfmisc_1(A_4849,B_4850,C_4851,D_4852),k1_xboole_0)
      | ~ r1_tarski(D_4852,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_315])).

tff(c_25404,plain,
    ( r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),k1_xboole_0)
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_25384])).

tff(c_25481,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_25404])).

tff(c_37647,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37562,c_25481])).

tff(c_37677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_37647])).

tff(c_37679,plain,(
    r1_tarski(k3_zfmisc_1('#skF_2','#skF_2','#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_31251])).

tff(c_24824,plain,(
    ! [A_4813] : r1_tarski(k1_xboole_0,A_4813) ),
    inference(splitRight,[status(thm)],[c_523])).

tff(c_24827,plain,(
    ! [A_4813] :
      ( k1_xboole_0 = A_4813
      | ~ r1_tarski(A_4813,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24824,c_2])).

tff(c_37864,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37679,c_24827])).

tff(c_37967,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_37864,c_174])).

tff(c_37973,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_37967])).

tff(c_38147,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_37973,c_8])).

tff(c_38202,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38147,c_25481])).

tff(c_38232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_38202])).

tff(c_38233,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_37967])).

tff(c_38287,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38233,c_25481])).

tff(c_38317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_38287])).

tff(c_38319,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_25435])).

tff(c_38330,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_38319,c_30])).

tff(c_38320,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38319,c_42])).

tff(c_38342,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_38320,c_30])).

tff(c_38388,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38330,c_38342])).

tff(c_38389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38388])).

tff(c_38391,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_25404])).

tff(c_38418,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38391,c_24827])).

tff(c_38422,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_25435])).

tff(c_38604,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38418,c_38422])).

tff(c_38390,plain,(
    r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_25404])).

tff(c_38683,plain,(
    r1_tarski(k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38418,c_38390])).

tff(c_38439,plain,(
    ! [A_4813] :
      ( A_4813 = '#skF_2'
      | ~ r1_tarski(A_4813,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38418,c_38418,c_24827])).

tff(c_38686,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38683,c_38439])).

tff(c_38692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38604,c_38686])).

tff(c_38694,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_25435])).

tff(c_38876,plain,(
    k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38418,c_38694])).

tff(c_426,plain,(
    ! [D_77,A_74,B_75,C_76] :
      ( k1_xboole_0 = D_77
      | k3_zfmisc_1(A_74,B_75,C_76) = k1_xboole_0
      | k4_zfmisc_1(A_74,B_75,C_76,D_77) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_8])).

tff(c_40472,plain,(
    ! [D_5367,A_5368,B_5369,C_5370] :
      ( D_5367 = '#skF_2'
      | k3_zfmisc_1(A_5368,B_5369,C_5370) = '#skF_2'
      | k4_zfmisc_1(A_5368,B_5369,C_5370,D_5367) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38418,c_38418,c_38418,c_426])).

tff(c_40487,plain,
    ( '#skF_2' = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_38876,c_40472])).

tff(c_40498,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40487])).

tff(c_38996,plain,(
    ! [C_47,A_45,B_46] :
      ( C_47 = '#skF_2'
      | k2_zfmisc_1(A_45,B_46) = '#skF_2'
      | k3_zfmisc_1(A_45,B_46,C_47) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38418,c_38418,c_38418,c_174])).

tff(c_40520,plain,
    ( '#skF_2' = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_40498,c_38996])).

tff(c_40532,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40520])).

tff(c_38720,plain,(
    ! [B_4,A_3] :
      ( B_4 = '#skF_2'
      | A_3 = '#skF_2'
      | k2_zfmisc_1(A_3,B_4) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38418,c_38418,c_38418,c_8])).

tff(c_40574,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_40532,c_38720])).

tff(c_40619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_40574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:34:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.11/4.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.11/4.58  
% 13.11/4.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.11/4.58  %$ r1_tarski > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 13.11/4.58  
% 13.11/4.58  %Foreground sorts:
% 13.11/4.58  
% 13.11/4.58  
% 13.11/4.58  %Background operators:
% 13.11/4.58  
% 13.11/4.58  
% 13.11/4.58  %Foreground operators:
% 13.11/4.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.11/4.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.11/4.58  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 13.11/4.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.11/4.58  tff('#skF_2', type, '#skF_2': $i).
% 13.11/4.58  tff('#skF_1', type, '#skF_1': $i).
% 13.11/4.58  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 13.11/4.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.11/4.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.11/4.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.11/4.58  
% 13.11/4.61  tff(f_86, negated_conjecture, ~(![A, B]: ((k4_zfmisc_1(A, A, A, A) = k4_zfmisc_1(B, B, B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_mcart_1)).
% 13.11/4.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.11/4.61  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.11/4.61  tff(f_66, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 13.11/4.61  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 13.11/4.61  tff(f_81, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 13.11/4.61  tff(f_62, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 13.11/4.61  tff(f_48, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 13.11/4.61  tff(f_64, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 13.11/4.61  tff(c_40, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.11/4.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.11/4.61  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.11/4.61  tff(c_42, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.11/4.61  tff(c_393, plain, (![A_74, B_75, C_76, D_77]: (k2_zfmisc_1(k3_zfmisc_1(A_74, B_75, C_76), D_77)=k4_zfmisc_1(A_74, B_75, C_76, D_77))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.11/4.61  tff(c_20, plain, (![A_8, C_10, B_9]: (r1_tarski(k2_zfmisc_1(A_8, C_10), k2_zfmisc_1(B_9, C_10)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.11/4.61  tff(c_30926, plain, (![C_5081, B_5084, B_5082, A_5083, D_5080]: (r1_tarski(k4_zfmisc_1(A_5083, B_5084, C_5081, D_5080), k2_zfmisc_1(B_5082, D_5080)) | ~r1_tarski(k3_zfmisc_1(A_5083, B_5084, C_5081), B_5082))), inference(superposition, [status(thm), theory('equality')], [c_393, c_20])).
% 13.11/4.61  tff(c_31229, plain, (![B_5092]: (r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), k2_zfmisc_1(B_5092, '#skF_2')) | ~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), B_5092))), inference(superposition, [status(thm), theory('equality')], [c_42, c_30926])).
% 13.11/4.61  tff(c_31251, plain, (r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_xboole_0) | ~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_31229])).
% 13.11/4.61  tff(c_32992, plain, (~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_31251])).
% 13.11/4.61  tff(c_680, plain, (![A_100, B_101, C_102, D_103]: (k4_zfmisc_1(A_100, B_101, C_102, D_103)!=k1_xboole_0 | k1_xboole_0=D_103 | k1_xboole_0=C_102 | k1_xboole_0=B_101 | k1_xboole_0=A_100)), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.11/4.61  tff(c_683, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_42, c_680])).
% 13.11/4.61  tff(c_953, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_683])).
% 13.11/4.61  tff(c_9596, plain, (![C_435, A_433, D_434, A_436, B_437]: (r1_tarski(k2_zfmisc_1(A_433, D_434), k4_zfmisc_1(A_436, B_437, C_435, D_434)) | ~r1_tarski(A_433, k3_zfmisc_1(A_436, B_437, C_435)))), inference(superposition, [status(thm), theory('equality')], [c_393, c_20])).
% 13.11/4.61  tff(c_10325, plain, (![A_448]: (r1_tarski(k2_zfmisc_1(A_448, '#skF_2'), k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')) | ~r1_tarski(A_448, k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_9596])).
% 13.11/4.61  tff(c_10355, plain, (r1_tarski(k1_xboole_0, k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')) | ~r1_tarski(k1_xboole_0, k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_10325])).
% 13.11/4.61  tff(c_10471, plain, (~r1_tarski(k1_xboole_0, k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_10355])).
% 13.11/4.61  tff(c_10747, plain, (![B_462, D_458, A_461, C_459, B_460]: (r1_tarski(k4_zfmisc_1(A_461, B_462, C_459, D_458), k2_zfmisc_1(B_460, D_458)) | ~r1_tarski(k3_zfmisc_1(A_461, B_462, C_459), B_460))), inference(superposition, [status(thm), theory('equality')], [c_393, c_20])).
% 13.11/4.61  tff(c_10855, plain, (![B_463]: (r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), k2_zfmisc_1(B_463, '#skF_2')) | ~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), B_463))), inference(superposition, [status(thm), theory('equality')], [c_42, c_10747])).
% 13.11/4.61  tff(c_10885, plain, (r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_xboole_0) | ~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_10855])).
% 13.11/4.61  tff(c_11014, plain, (~r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10885])).
% 13.11/4.61  tff(c_420, plain, (![A_74, A_8, D_77, B_75, C_76]: (r1_tarski(k2_zfmisc_1(A_8, D_77), k4_zfmisc_1(A_74, B_75, C_76, D_77)) | ~r1_tarski(A_8, k3_zfmisc_1(A_74, B_75, C_76)))), inference(superposition, [status(thm), theory('equality')], [c_393, c_20])).
% 13.11/4.61  tff(c_28, plain, (![A_18, B_19, C_20, D_21]: (k2_zfmisc_1(k3_zfmisc_1(A_18, B_19, C_20), D_21)=k4_zfmisc_1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.11/4.61  tff(c_1129, plain, (![B_131, D_132, A_133, C_134]: (r1_tarski(B_131, D_132) | k2_zfmisc_1(A_133, B_131)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_133, B_131), k2_zfmisc_1(C_134, D_132)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.11/4.61  tff(c_12188, plain, (![C_502, B_504, D_503, A_501, B_499, A_500]: (r1_tarski(B_499, D_503) | k2_zfmisc_1(A_500, B_499)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_500, B_499), k4_zfmisc_1(A_501, B_504, C_502, D_503)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1129])).
% 13.11/4.61  tff(c_12927, plain, (![B_516, A_517]: (r1_tarski(B_516, '#skF_2') | k2_zfmisc_1(A_517, B_516)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_517, B_516), k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_12188])).
% 13.11/4.61  tff(c_12988, plain, (![A_8]: (r1_tarski('#skF_1', '#skF_2') | k2_zfmisc_1(A_8, '#skF_1')=k1_xboole_0 | ~r1_tarski(A_8, k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_420, c_12927])).
% 13.11/4.61  tff(c_14612, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_12988])).
% 13.11/4.61  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.11/4.61  tff(c_14614, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_14612, c_2])).
% 13.11/4.61  tff(c_14617, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_14614])).
% 13.11/4.61  tff(c_9670, plain, (![A_433]: (r1_tarski(k2_zfmisc_1(A_433, '#skF_2'), k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')) | ~r1_tarski(A_433, k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_9596])).
% 13.11/4.61  tff(c_12294, plain, (![A_433]: (r1_tarski('#skF_2', '#skF_1') | k2_zfmisc_1(A_433, '#skF_2')=k1_xboole_0 | ~r1_tarski(A_433, k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_9670, c_12188])).
% 13.11/4.61  tff(c_14851, plain, (![A_551]: (k2_zfmisc_1(A_551, '#skF_2')=k1_xboole_0 | ~r1_tarski(A_551, k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_14617, c_12294])).
% 13.11/4.61  tff(c_14910, plain, (k2_zfmisc_1(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_14851])).
% 13.11/4.61  tff(c_456, plain, (![B_78, A_79, C_80]: (~r1_tarski(k2_zfmisc_1(B_78, A_79), k2_zfmisc_1(C_80, A_79)) | r1_tarski(B_78, C_80) | k1_xboole_0=A_79)), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.11/4.61  tff(c_487, plain, (![B_78, B_4]: (~r1_tarski(k2_zfmisc_1(B_78, B_4), k1_xboole_0) | r1_tarski(B_78, k1_xboole_0) | k1_xboole_0=B_4)), inference(superposition, [status(thm), theory('equality')], [c_12, c_456])).
% 13.11/4.61  tff(c_15080, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), k1_xboole_0) | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_14910, c_487])).
% 13.11/4.61  tff(c_15202, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), k1_xboole_0) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_15080])).
% 13.11/4.61  tff(c_15203, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_11014, c_15202])).
% 13.11/4.61  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.11/4.61  tff(c_301, plain, (![C_61, A_62, B_63]: (r1_tarski(k2_zfmisc_1(C_61, A_62), k2_zfmisc_1(C_61, B_63)) | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.11/4.61  tff(c_312, plain, (![A_3, B_63]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_3, B_63)) | ~r1_tarski(k1_xboole_0, B_63))), inference(superposition, [status(thm), theory('equality')], [c_10, c_301])).
% 13.11/4.61  tff(c_1703, plain, (![A_160, B_161, C_162, D_163]: (r1_tarski(k1_xboole_0, k4_zfmisc_1(A_160, B_161, C_162, D_163)) | ~r1_tarski(k1_xboole_0, D_163))), inference(superposition, [status(thm), theory('equality')], [c_393, c_312])).
% 13.11/4.61  tff(c_1723, plain, (r1_tarski(k1_xboole_0, k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')) | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_1703])).
% 13.11/4.61  tff(c_1768, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_1723])).
% 13.11/4.61  tff(c_15312, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15203, c_1768])).
% 13.11/4.61  tff(c_15364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_15312])).
% 13.11/4.61  tff(c_15367, plain, (![A_552]: (k2_zfmisc_1(A_552, '#skF_1')=k1_xboole_0 | ~r1_tarski(A_552, k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_12988])).
% 13.11/4.61  tff(c_15426, plain, (k2_zfmisc_1(k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_15367])).
% 13.11/4.61  tff(c_15614, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15426, c_28])).
% 13.11/4.61  tff(c_15714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_953, c_15614])).
% 13.11/4.61  tff(c_15716, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_10885])).
% 13.11/4.61  tff(c_244, plain, (![A_54, C_55, B_56]: (r1_tarski(k2_zfmisc_1(A_54, C_55), k2_zfmisc_1(B_56, C_55)) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.11/4.61  tff(c_264, plain, (![A_54, B_4]: (r1_tarski(k2_zfmisc_1(A_54, B_4), k1_xboole_0) | ~r1_tarski(A_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_244])).
% 13.11/4.61  tff(c_315, plain, (![A_3, A_62]: (r1_tarski(k2_zfmisc_1(A_3, A_62), k1_xboole_0) | ~r1_tarski(A_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_301])).
% 13.11/4.61  tff(c_954, plain, (![B_114, B_115]: (~r1_tarski(k2_zfmisc_1(B_114, B_115), k1_xboole_0) | r1_tarski(B_114, k1_xboole_0) | k1_xboole_0=B_115)), inference(superposition, [status(thm), theory('equality')], [c_12, c_456])).
% 13.11/4.61  tff(c_983, plain, (![A_3, A_62]: (r1_tarski(A_3, k1_xboole_0) | k1_xboole_0=A_62 | ~r1_tarski(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_315, c_954])).
% 13.11/4.61  tff(c_991, plain, (![A_116]: (k1_xboole_0=A_116 | ~r1_tarski(A_116, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_983])).
% 13.11/4.61  tff(c_1010, plain, (![A_117, A_118]: (k2_zfmisc_1(A_117, A_118)=k1_xboole_0 | ~r1_tarski(A_118, k1_xboole_0))), inference(resolution, [status(thm)], [c_315, c_991])).
% 13.11/4.61  tff(c_1022, plain, (![A_117, A_54, B_4]: (k2_zfmisc_1(A_117, k2_zfmisc_1(A_54, B_4))=k1_xboole_0 | ~r1_tarski(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_264, c_1010])).
% 13.11/4.61  tff(c_550, plain, (![A_84, B_85, C_86]: (~r1_tarski(k2_zfmisc_1(A_84, B_85), k2_zfmisc_1(A_84, C_86)) | r1_tarski(B_85, C_86) | k1_xboole_0=A_84)), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.11/4.61  tff(c_1547, plain, (![A_148, C_149]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_148, C_149)) | r1_tarski(k1_xboole_0, C_149) | k1_xboole_0=A_148)), inference(superposition, [status(thm), theory('equality')], [c_10, c_550])).
% 13.11/4.61  tff(c_1553, plain, (![A_54, B_4, A_117]: (~r1_tarski(k1_xboole_0, k1_xboole_0) | r1_tarski(k1_xboole_0, k2_zfmisc_1(A_54, B_4)) | k1_xboole_0=A_117 | ~r1_tarski(A_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1022, c_1547])).
% 13.11/4.61  tff(c_1581, plain, (![A_54, B_4, A_117]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_54, B_4)) | k1_xboole_0=A_117 | ~r1_tarski(A_54, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1553])).
% 13.11/4.61  tff(c_3649, plain, (![A_231, B_232]: (r1_tarski(k1_xboole_0, k2_zfmisc_1(A_231, B_232)) | ~r1_tarski(A_231, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1581])).
% 13.11/4.61  tff(c_484, plain, (![C_80, B_4]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(C_80, B_4)) | r1_tarski(k1_xboole_0, C_80) | k1_xboole_0=B_4)), inference(superposition, [status(thm), theory('equality')], [c_12, c_456])).
% 13.11/4.61  tff(c_3719, plain, (![A_231, B_232]: (r1_tarski(k1_xboole_0, A_231) | k1_xboole_0=B_232 | ~r1_tarski(A_231, k1_xboole_0))), inference(resolution, [status(thm)], [c_3649, c_484])).
% 13.11/4.61  tff(c_3730, plain, (![A_231]: (r1_tarski(k1_xboole_0, A_231) | ~r1_tarski(A_231, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_3719])).
% 13.11/4.61  tff(c_15849, plain, (r1_tarski(k1_xboole_0, k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_15716, c_3730])).
% 13.11/4.61  tff(c_15874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10471, c_15849])).
% 13.11/4.61  tff(c_15876, plain, (r1_tarski(k1_xboole_0, k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'))), inference(splitRight, [status(thm)], [c_10355])).
% 13.11/4.61  tff(c_504, plain, (![C_81, B_82]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(C_81, B_82)) | r1_tarski(k1_xboole_0, C_81) | k1_xboole_0=B_82)), inference(superposition, [status(thm), theory('equality')], [c_12, c_456])).
% 13.11/4.61  tff(c_523, plain, (![A_3, B_63]: (r1_tarski(k1_xboole_0, A_3) | k1_xboole_0=B_63 | ~r1_tarski(k1_xboole_0, B_63))), inference(resolution, [status(thm)], [c_312, c_504])).
% 13.11/4.61  tff(c_530, plain, (![B_63]: (k1_xboole_0=B_63 | ~r1_tarski(k1_xboole_0, B_63))), inference(splitLeft, [status(thm)], [c_523])).
% 13.11/4.61  tff(c_15912, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_15876, c_530])).
% 13.11/4.61  tff(c_165, plain, (![A_45, B_46, C_47]: (k2_zfmisc_1(k2_zfmisc_1(A_45, B_46), C_47)=k3_zfmisc_1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.11/4.61  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.11/4.61  tff(c_174, plain, (![C_47, A_45, B_46]: (k1_xboole_0=C_47 | k2_zfmisc_1(A_45, B_46)=k1_xboole_0 | k3_zfmisc_1(A_45, B_46, C_47)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_165, c_8])).
% 13.11/4.61  tff(c_16002, plain, (k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15912, c_174])).
% 13.11/4.61  tff(c_16042, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_16002])).
% 13.11/4.61  tff(c_16287, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_16042, c_8])).
% 13.11/4.61  tff(c_16354, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16287, c_1768])).
% 13.11/4.61  tff(c_16406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_16354])).
% 13.11/4.61  tff(c_16407, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_16002])).
% 13.11/4.61  tff(c_16473, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16407, c_1768])).
% 13.11/4.61  tff(c_16525, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_16473])).
% 13.11/4.61  tff(c_16527, plain, (![B_557]: (k1_xboole_0=B_557)), inference(splitRight, [status(thm)], [c_3719])).
% 13.11/4.61  tff(c_16676, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_16527, c_953])).
% 13.11/4.61  tff(c_16834, plain, (![A_834]: (k1_xboole_0=A_834)), inference(splitRight, [status(thm)], [c_1581])).
% 13.11/4.61  tff(c_16974, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_16834, c_953])).
% 13.11/4.61  tff(c_16976, plain, (r1_tarski(k1_xboole_0, '#skF_2')), inference(splitRight, [status(thm)], [c_1723])).
% 13.11/4.61  tff(c_17003, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_16976, c_530])).
% 13.11/4.61  tff(c_1639, plain, (![A_152, B_153, C_154, D_155]: (r1_tarski(k4_zfmisc_1(A_152, B_153, C_154, D_155), k1_xboole_0) | ~r1_tarski(D_155, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_393, c_315])).
% 13.11/4.61  tff(c_1659, plain, (r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_xboole_0) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_1639])).
% 13.11/4.61  tff(c_1749, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1659])).
% 13.11/4.61  tff(c_17007, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17003, c_1749])).
% 13.11/4.61  tff(c_17058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_17007])).
% 13.11/4.61  tff(c_17060, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1659])).
% 13.11/4.61  tff(c_990, plain, (![A_62]: (k1_xboole_0=A_62 | ~r1_tarski(A_62, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_983])).
% 13.11/4.61  tff(c_17171, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_17060, c_990])).
% 13.11/4.61  tff(c_17191, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17171, c_953])).
% 13.11/4.61  tff(c_34, plain, (![A_22, B_23, D_25]: (k4_zfmisc_1(A_22, B_23, k1_xboole_0, D_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.11/4.61  tff(c_17217, plain, (![A_22, B_23, D_25]: (k4_zfmisc_1(A_22, B_23, '#skF_2', D_25)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17171, c_17171, c_34])).
% 13.11/4.61  tff(c_17442, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17217, c_42])).
% 13.11/4.61  tff(c_17450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17191, c_17442])).
% 13.11/4.61  tff(c_17451, plain, (![A_3]: (r1_tarski(A_3, k1_xboole_0))), inference(splitRight, [status(thm)], [c_983])).
% 13.11/4.61  tff(c_17609, plain, (![A_1109, C_1110, B_1111, D_1112]: (r1_tarski(A_1109, C_1110) | k2_zfmisc_1(A_1109, B_1111)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_1109, B_1111), k2_zfmisc_1(C_1110, D_1112)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.11/4.61  tff(c_17645, plain, (![A_1109, A_3, B_1111]: (r1_tarski(A_1109, A_3) | k2_zfmisc_1(A_1109, B_1111)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_1109, B_1111), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_17609])).
% 13.11/4.61  tff(c_17673, plain, (![A_1113, A_1114, B_1115]: (r1_tarski(A_1113, A_1114) | k2_zfmisc_1(A_1113, B_1115)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17451, c_17645])).
% 13.11/4.61  tff(c_17846, plain, (![B_1115, A_1113, A_1114]: (k1_xboole_0=B_1115 | k1_xboole_0=A_1113 | r1_tarski(A_1113, A_1114))), inference(superposition, [status(thm), theory('equality')], [c_17673, c_8])).
% 13.11/4.61  tff(c_17852, plain, (![A_1113, A_1114]: (k1_xboole_0=A_1113 | r1_tarski(A_1113, A_1114))), inference(splitLeft, [status(thm)], [c_17846])).
% 13.11/4.61  tff(c_17853, plain, (![A_1116, A_1117]: (k1_xboole_0=A_1116 | r1_tarski(A_1116, A_1117))), inference(splitLeft, [status(thm)], [c_17846])).
% 13.11/4.61  tff(c_17925, plain, (![A_1119, A_1118]: (A_1119=A_1118 | ~r1_tarski(A_1118, A_1119) | k1_xboole_0=A_1119)), inference(resolution, [status(thm)], [c_17853, c_2])).
% 13.11/4.61  tff(c_18078, plain, (![A_1121, A_1120]: (A_1121=A_1120 | k1_xboole_0=A_1120 | k1_xboole_0=A_1121)), inference(resolution, [status(thm)], [c_17852, c_17925])).
% 13.11/4.61  tff(c_17538, plain, (![A_1101, B_1102, C_1103, D_1104]: (r1_tarski(k1_xboole_0, k4_zfmisc_1(A_1101, B_1102, C_1103, D_1104)) | ~r1_tarski(k1_xboole_0, D_1104))), inference(superposition, [status(thm), theory('equality')], [c_393, c_312])).
% 13.11/4.61  tff(c_17558, plain, (r1_tarski(k1_xboole_0, k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')) | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_17538])).
% 13.11/4.61  tff(c_17914, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_17558])).
% 13.11/4.61  tff(c_20991, plain, (![A_2742, A_2743]: (~r1_tarski(A_2742, '#skF_2') | A_2743=A_2742 | k1_xboole_0=A_2743)), inference(superposition, [status(thm), theory('equality')], [c_18078, c_17914])).
% 13.11/4.61  tff(c_21082, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_20991])).
% 13.11/4.61  tff(c_21083, plain, (![A_3]: (r1_tarski(A_3, '#skF_1') | '#skF_2'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_21082, c_17451])).
% 13.11/4.61  tff(c_21586, plain, (![A_3289]: (r1_tarski(A_3289, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_40, c_21083])).
% 13.11/4.61  tff(c_21637, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_21586, c_530])).
% 13.11/4.61  tff(c_21283, plain, ('#skF_2'='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_20991])).
% 13.11/4.61  tff(c_21284, plain, (![A_22, B_23, D_25]: (k4_zfmisc_1(A_22, B_23, '#skF_1', D_25)=k1_xboole_0 | '#skF_2'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_21283, c_34])).
% 13.11/4.61  tff(c_21427, plain, (![A_22, B_23, D_25]: (k4_zfmisc_1(A_22, B_23, '#skF_1', D_25)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_40, c_21284])).
% 13.11/4.61  tff(c_21998, plain, (![A_22, B_23, D_25]: (k4_zfmisc_1(A_22, B_23, '#skF_1', D_25)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21637, c_21427])).
% 13.11/4.61  tff(c_21028, plain, (![A_2780]: (A_2780='#skF_2' | k1_xboole_0=A_2780)), inference(resolution, [status(thm)], [c_6, c_20991])).
% 13.11/4.61  tff(c_21380, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_21028, c_953])).
% 13.11/4.61  tff(c_24348, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21998, c_21380])).
% 13.11/4.61  tff(c_24349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_24348])).
% 13.11/4.61  tff(c_24350, plain, (r1_tarski(k1_xboole_0, k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(splitRight, [status(thm)], [c_17558])).
% 13.11/4.61  tff(c_24398, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_24350, c_530])).
% 13.11/4.61  tff(c_24411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_953, c_24398])).
% 13.11/4.61  tff(c_24413, plain, (![B_4642]: (k1_xboole_0=B_4642)), inference(splitRight, [status(thm)], [c_17846])).
% 13.11/4.61  tff(c_24486, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_24413, c_953])).
% 13.11/4.61  tff(c_24488, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_683])).
% 13.11/4.61  tff(c_30, plain, (![A_22, B_23, C_24, D_25]: (k4_zfmisc_1(A_22, B_23, C_24, D_25)!=k1_xboole_0 | k1_xboole_0=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.11/4.61  tff(c_24496, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_24488, c_30])).
% 13.11/4.61  tff(c_24487, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_683])).
% 13.11/4.61  tff(c_24813, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24496, c_24496, c_24496, c_24496, c_24487])).
% 13.11/4.61  tff(c_24814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_40, c_40, c_24813])).
% 13.11/4.61  tff(c_24815, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(splitRight, [status(thm)], [c_523])).
% 13.11/4.61  tff(c_25432, plain, (![A_4853, B_4854, C_4855, D_4856]: (k4_zfmisc_1(A_4853, B_4854, C_4855, D_4856)!=k1_xboole_0 | k1_xboole_0=D_4856 | k1_xboole_0=C_4855 | k1_xboole_0=B_4854 | k1_xboole_0=A_4853)), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.11/4.61  tff(c_25435, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_42, c_25432])).
% 13.11/4.61  tff(c_25886, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_25435])).
% 13.11/4.61  tff(c_31777, plain, (![B_5107, A_5103, C_5105, A_5106, D_5104]: (r1_tarski(k2_zfmisc_1(A_5103, D_5104), k4_zfmisc_1(A_5106, B_5107, C_5105, D_5104)) | ~r1_tarski(A_5103, k3_zfmisc_1(A_5106, B_5107, C_5105)))), inference(superposition, [status(thm), theory('equality')], [c_393, c_20])).
% 13.11/4.61  tff(c_31842, plain, (![A_5103]: (r1_tarski(k2_zfmisc_1(A_5103, '#skF_2'), k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')) | ~r1_tarski(A_5103, k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_31777])).
% 13.11/4.61  tff(c_25112, plain, (![B_4834, D_4835, A_4836, C_4837]: (r1_tarski(B_4834, D_4835) | k2_zfmisc_1(A_4836, B_4834)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_4836, B_4834), k2_zfmisc_1(C_4837, D_4835)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.11/4.61  tff(c_34711, plain, (![A_5184, B_5183, D_5186, A_5182, B_5187, C_5185]: (r1_tarski(B_5183, D_5186) | k2_zfmisc_1(A_5182, B_5183)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_5182, B_5183), k4_zfmisc_1(A_5184, B_5187, C_5185, D_5186)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_25112])).
% 13.11/4.61  tff(c_34823, plain, (![A_5103]: (r1_tarski('#skF_2', '#skF_1') | k2_zfmisc_1(A_5103, '#skF_2')=k1_xboole_0 | ~r1_tarski(A_5103, k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_31842, c_34711])).
% 13.11/4.61  tff(c_35920, plain, (r1_tarski('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_34823])).
% 13.11/4.61  tff(c_35922, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_35920, c_2])).
% 13.11/4.61  tff(c_35925, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_35922])).
% 13.11/4.61  tff(c_34852, plain, (![B_5188, A_5189]: (r1_tarski(B_5188, '#skF_2') | k2_zfmisc_1(A_5189, B_5188)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_5189, B_5188), k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_34711])).
% 13.11/4.61  tff(c_34919, plain, (![A_8]: (r1_tarski('#skF_1', '#skF_2') | k2_zfmisc_1(A_8, '#skF_1')=k1_xboole_0 | ~r1_tarski(A_8, k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_420, c_34852])).
% 13.11/4.61  tff(c_37015, plain, (![A_5224]: (k2_zfmisc_1(A_5224, '#skF_1')=k1_xboole_0 | ~r1_tarski(A_5224, k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_35925, c_34919])).
% 13.11/4.61  tff(c_37096, plain, (k2_zfmisc_1(k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_37015])).
% 13.11/4.61  tff(c_34800, plain, (![B_5183, A_5182]: (r1_tarski(B_5183, '#skF_2') | k2_zfmisc_1(A_5182, B_5183)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_5182, B_5183), k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_34711])).
% 13.11/4.61  tff(c_37124, plain, (r1_tarski('#skF_1', '#skF_2') | k2_zfmisc_1(k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1'), '#skF_1')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_37096, c_34800])).
% 13.11/4.61  tff(c_37277, plain, (r1_tarski('#skF_1', '#skF_2') | k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24815, c_28, c_37124])).
% 13.11/4.61  tff(c_37279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25886, c_35925, c_37277])).
% 13.11/4.61  tff(c_37282, plain, (![A_5225]: (k2_zfmisc_1(A_5225, '#skF_2')=k1_xboole_0 | ~r1_tarski(A_5225, k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')))), inference(splitRight, [status(thm)], [c_34823])).
% 13.11/4.61  tff(c_37351, plain, (k2_zfmisc_1(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_37282])).
% 13.11/4.61  tff(c_37463, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), k1_xboole_0) | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_37351, c_487])).
% 13.11/4.61  tff(c_37561, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), k1_xboole_0) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24815, c_37463])).
% 13.11/4.61  tff(c_37562, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_32992, c_37561])).
% 13.11/4.61  tff(c_25384, plain, (![A_4849, B_4850, C_4851, D_4852]: (r1_tarski(k4_zfmisc_1(A_4849, B_4850, C_4851, D_4852), k1_xboole_0) | ~r1_tarski(D_4852, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_393, c_315])).
% 13.11/4.61  tff(c_25404, plain, (r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_xboole_0) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_25384])).
% 13.11/4.61  tff(c_25481, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_25404])).
% 13.11/4.61  tff(c_37647, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37562, c_25481])).
% 13.11/4.61  tff(c_37677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_37647])).
% 13.11/4.61  tff(c_37679, plain, (r1_tarski(k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_31251])).
% 13.11/4.61  tff(c_24824, plain, (![A_4813]: (r1_tarski(k1_xboole_0, A_4813))), inference(splitRight, [status(thm)], [c_523])).
% 13.11/4.61  tff(c_24827, plain, (![A_4813]: (k1_xboole_0=A_4813 | ~r1_tarski(A_4813, k1_xboole_0))), inference(resolution, [status(thm)], [c_24824, c_2])).
% 13.11/4.61  tff(c_37864, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_37679, c_24827])).
% 13.11/4.61  tff(c_37967, plain, (k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_37864, c_174])).
% 13.11/4.61  tff(c_37973, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_37967])).
% 13.11/4.61  tff(c_38147, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_37973, c_8])).
% 13.11/4.61  tff(c_38202, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38147, c_25481])).
% 13.11/4.61  tff(c_38232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_38202])).
% 13.11/4.61  tff(c_38233, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_37967])).
% 13.11/4.61  tff(c_38287, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38233, c_25481])).
% 13.11/4.61  tff(c_38317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_38287])).
% 13.11/4.61  tff(c_38319, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_25435])).
% 13.11/4.61  tff(c_38330, plain, (k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_38319, c_30])).
% 13.11/4.61  tff(c_38320, plain, (k4_zfmisc_1('#skF_2', '#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38319, c_42])).
% 13.11/4.61  tff(c_38342, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_38320, c_30])).
% 13.11/4.61  tff(c_38388, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38330, c_38342])).
% 13.11/4.61  tff(c_38389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38388])).
% 13.11/4.61  tff(c_38391, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_25404])).
% 13.11/4.61  tff(c_38418, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38391, c_24827])).
% 13.11/4.61  tff(c_38422, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_25435])).
% 13.11/4.61  tff(c_38604, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38418, c_38422])).
% 13.11/4.61  tff(c_38390, plain, (r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_25404])).
% 13.11/4.61  tff(c_38683, plain, (r1_tarski(k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38418, c_38390])).
% 13.11/4.61  tff(c_38439, plain, (![A_4813]: (A_4813='#skF_2' | ~r1_tarski(A_4813, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38418, c_38418, c_24827])).
% 13.11/4.61  tff(c_38686, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_38683, c_38439])).
% 13.11/4.61  tff(c_38692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38604, c_38686])).
% 13.11/4.61  tff(c_38694, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_25435])).
% 13.11/4.61  tff(c_38876, plain, (k4_zfmisc_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38418, c_38694])).
% 13.11/4.61  tff(c_426, plain, (![D_77, A_74, B_75, C_76]: (k1_xboole_0=D_77 | k3_zfmisc_1(A_74, B_75, C_76)=k1_xboole_0 | k4_zfmisc_1(A_74, B_75, C_76, D_77)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_393, c_8])).
% 13.11/4.61  tff(c_40472, plain, (![D_5367, A_5368, B_5369, C_5370]: (D_5367='#skF_2' | k3_zfmisc_1(A_5368, B_5369, C_5370)='#skF_2' | k4_zfmisc_1(A_5368, B_5369, C_5370, D_5367)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38418, c_38418, c_38418, c_426])).
% 13.11/4.61  tff(c_40487, plain, ('#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_38876, c_40472])).
% 13.11/4.61  tff(c_40498, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_40, c_40487])).
% 13.11/4.61  tff(c_38996, plain, (![C_47, A_45, B_46]: (C_47='#skF_2' | k2_zfmisc_1(A_45, B_46)='#skF_2' | k3_zfmisc_1(A_45, B_46, C_47)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38418, c_38418, c_38418, c_174])).
% 13.11/4.61  tff(c_40520, plain, ('#skF_2'='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_40498, c_38996])).
% 13.11/4.61  tff(c_40532, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_40, c_40520])).
% 13.11/4.61  tff(c_38720, plain, (![B_4, A_3]: (B_4='#skF_2' | A_3='#skF_2' | k2_zfmisc_1(A_3, B_4)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38418, c_38418, c_38418, c_8])).
% 13.11/4.61  tff(c_40574, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_40532, c_38720])).
% 13.11/4.61  tff(c_40619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_40574])).
% 13.11/4.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.11/4.61  
% 13.11/4.61  Inference rules
% 13.11/4.61  ----------------------
% 13.11/4.61  #Ref     : 0
% 13.11/4.61  #Sup     : 9441
% 13.11/4.61  #Fact    : 34
% 13.11/4.61  #Define  : 0
% 13.11/4.61  #Split   : 34
% 13.11/4.61  #Chain   : 0
% 13.11/4.61  #Close   : 0
% 13.11/4.61  
% 13.11/4.61  Ordering : KBO
% 13.11/4.61  
% 13.11/4.61  Simplification rules
% 13.11/4.61  ----------------------
% 13.11/4.61  #Subsume      : 2036
% 13.11/4.61  #Demod        : 6958
% 13.11/4.61  #Tautology    : 4869
% 13.11/4.61  #SimpNegUnit  : 135
% 13.11/4.61  #BackRed      : 964
% 13.11/4.61  
% 13.11/4.61  #Partial instantiations: 1389
% 13.11/4.61  #Strategies tried      : 1
% 13.11/4.61  
% 13.11/4.61  Timing (in seconds)
% 13.11/4.61  ----------------------
% 13.11/4.62  Preprocessing        : 0.32
% 13.11/4.62  Parsing              : 0.17
% 13.11/4.62  CNF conversion       : 0.02
% 13.11/4.62  Main loop            : 3.51
% 13.11/4.62  Inferencing          : 0.99
% 13.11/4.62  Reduction            : 1.02
% 13.11/4.62  Demodulation         : 0.72
% 13.11/4.62  BG Simplification    : 0.11
% 13.11/4.62  Subsumption          : 1.17
% 13.11/4.62  Abstraction          : 0.14
% 13.11/4.62  MUC search           : 0.00
% 13.11/4.62  Cooper               : 0.00
% 13.11/4.62  Total                : 3.89
% 13.11/4.62  Index Insertion      : 0.00
% 13.11/4.62  Index Deletion       : 0.00
% 13.11/4.62  Index Matching       : 0.00
% 13.11/4.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
