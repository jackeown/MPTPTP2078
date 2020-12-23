%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:22 EST 2020

% Result     : Theorem 7.46s
% Output     : CNFRefutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 443 expanded)
%              Number of leaves         :   27 ( 159 expanded)
%              Depth                    :   20
%              Number of atoms          :  207 ( 739 expanded)
%              Number of equality atoms :  100 ( 350 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_54,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_122,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_52,plain,
    ( ~ r1_tarski('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_88,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_126,plain,(
    k4_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_88])).

tff(c_32,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_157,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_1'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_137,plain,(
    ! [D_42,B_43,A_44] :
      ( ~ r2_hidden(D_42,B_43)
      | ~ r2_hidden(D_42,k4_xboole_0(A_44,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_140,plain,(
    ! [D_42,A_16] :
      ( ~ r2_hidden(D_42,k1_xboole_0)
      | ~ r2_hidden(D_42,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_137])).

tff(c_364,plain,(
    ! [B_69,A_70] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_69),A_70)
      | r1_tarski(k1_xboole_0,B_69) ) ),
    inference(resolution,[status(thm)],[c_157,c_140])).

tff(c_369,plain,(
    ! [B_4] : r1_tarski(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_364])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    ! [A_19] : k2_zfmisc_1(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_442,plain,(
    ! [C_76,A_77,B_78] :
      ( r1_tarski(k2_zfmisc_1(C_76,A_77),k2_zfmisc_1(C_76,B_78))
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_463,plain,(
    ! [A_79,A_80] :
      ( r1_tarski(k2_zfmisc_1(A_79,A_80),k1_xboole_0)
      | ~ r1_tarski(A_80,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_442])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_466,plain,(
    ! [A_79,A_80] :
      ( k4_xboole_0(k2_zfmisc_1(A_79,A_80),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_80,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_463,c_30])).

tff(c_478,plain,(
    ! [A_81,A_82] :
      ( k2_zfmisc_1(A_81,A_82) = k1_xboole_0
      | ~ r1_tarski(A_82,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_466])).

tff(c_489,plain,(
    ! [A_81,A_14] :
      ( k2_zfmisc_1(A_81,A_14) = k1_xboole_0
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_478])).

tff(c_496,plain,(
    ! [A_81,A_14] :
      ( k2_zfmisc_1(A_81,A_14) = k1_xboole_0
      | k1_xboole_0 != A_14 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_489])).

tff(c_1329,plain,(
    ! [A_121,B_122,C_123] :
      ( ~ r1_tarski(k2_zfmisc_1(A_121,B_122),k2_zfmisc_1(A_121,C_123))
      | r1_tarski(B_122,C_123)
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1366,plain,(
    ! [A_81,C_123,A_14] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_81,C_123))
      | r1_tarski(A_14,C_123)
      | k1_xboole_0 = A_81
      | k1_xboole_0 != A_14 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_1329])).

tff(c_1394,plain,(
    ! [A_14,C_123,A_81] :
      ( r1_tarski(A_14,C_123)
      | k1_xboole_0 = A_81
      | k1_xboole_0 != A_14 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_1366])).

tff(c_1402,plain,(
    ! [A_124,C_125] :
      ( r1_tarski(A_124,C_125)
      | k1_xboole_0 != A_124 ) ),
    inference(splitLeft,[status(thm)],[c_1394])).

tff(c_1428,plain,(
    ! [A_126,C_127] :
      ( k4_xboole_0(A_126,C_127) = k1_xboole_0
      | k1_xboole_0 != A_126 ) ),
    inference(resolution,[status(thm)],[c_1402,c_30])).

tff(c_34,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1448,plain,(
    ! [A_126,C_127] :
      ( k4_xboole_0(A_126,k1_xboole_0) = k3_xboole_0(A_126,C_127)
      | k1_xboole_0 != A_126 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1428,c_34])).

tff(c_1614,plain,(
    ! [C_127] : k3_xboole_0(k1_xboole_0,C_127) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1448])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_7990,plain,(
    ! [A_286,B_287,B_288] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_286,B_287),B_288),A_286)
      | r1_tarski(k4_xboole_0(A_286,B_287),B_288) ) ),
    inference(resolution,[status(thm)],[c_157,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8082,plain,(
    ! [A_289,B_290] : r1_tarski(k4_xboole_0(A_289,B_290),A_289) ),
    inference(resolution,[status(thm)],[c_7990,c_6])).

tff(c_8169,plain,(
    ! [A_289,B_290] : k4_xboole_0(k4_xboole_0(A_289,B_290),A_289) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8082,c_30])).

tff(c_8144,plain,(
    ! [A_17,B_18] : r1_tarski(k3_xboole_0(A_17,B_18),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_8082])).

tff(c_458,plain,(
    ! [C_76,A_77,B_78] :
      ( k4_xboole_0(k2_zfmisc_1(C_76,A_77),k2_zfmisc_1(C_76,B_78)) = k1_xboole_0
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_442,c_30])).

tff(c_2064,plain,(
    ! [A_142,C_143,B_144,D_145] : k3_xboole_0(k2_zfmisc_1(A_142,C_143),k2_zfmisc_1(B_144,D_145)) = k2_zfmisc_1(k3_xboole_0(A_142,B_144),k3_xboole_0(C_143,D_145)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_56,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_127,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_134,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_127])).

tff(c_220,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_241,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k4_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_220])).

tff(c_250,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_241])).

tff(c_2085,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2064,c_250])).

tff(c_5716,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k3_xboole_0('#skF_5','#skF_7') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2085,c_496])).

tff(c_5764,plain,(
    k3_xboole_0('#skF_5','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5716])).

tff(c_1750,plain,(
    ! [B_135,A_136,C_137] :
      ( ~ r1_tarski(k2_zfmisc_1(B_135,A_136),k2_zfmisc_1(C_137,A_136))
      | r1_tarski(B_135,C_137)
      | k1_xboole_0 = A_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_9445,plain,(
    ! [B_314,C_315,A_316] :
      ( r1_tarski(B_314,C_315)
      | k1_xboole_0 = A_316
      | k4_xboole_0(k2_zfmisc_1(B_314,A_316),k2_zfmisc_1(C_315,A_316)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_1750])).

tff(c_9472,plain,(
    ! [B_314] :
      ( r1_tarski(B_314,k3_xboole_0('#skF_4','#skF_6'))
      | k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0
      | k4_xboole_0(k2_zfmisc_1(B_314,k3_xboole_0('#skF_5','#skF_7')),k2_zfmisc_1('#skF_4','#skF_5')) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2085,c_9445])).

tff(c_9709,plain,(
    ! [B_320] :
      ( r1_tarski(B_320,k3_xboole_0('#skF_4','#skF_6'))
      | k4_xboole_0(k2_zfmisc_1(B_320,k3_xboole_0('#skF_5','#skF_7')),k2_zfmisc_1('#skF_4','#skF_5')) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_5764,c_9472])).

tff(c_9721,plain,
    ( r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski(k3_xboole_0('#skF_5','#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_9709])).

tff(c_9786,plain,(
    r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8144,c_9721])).

tff(c_9842,plain,(
    k4_xboole_0('#skF_4',k3_xboole_0('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9786,c_30])).

tff(c_235,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_220])).

tff(c_9875,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9842,c_235])).

tff(c_1117,plain,(
    ! [A_112,B_113] : k4_xboole_0(A_112,k3_xboole_0(A_112,B_113)) = k3_xboole_0(A_112,k4_xboole_0(A_112,B_113)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_220])).

tff(c_1158,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1117])).

tff(c_9970,plain,(
    k3_xboole_0(k4_xboole_0('#skF_4','#skF_6'),k4_xboole_0(k4_xboole_0('#skF_4','#skF_6'),'#skF_4')) = k4_xboole_0(k4_xboole_0('#skF_4','#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9875,c_1158])).

tff(c_10011,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1614,c_2,c_8169,c_32,c_9970])).

tff(c_10013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_10011])).

tff(c_10015,plain,(
    ! [A_321] : k1_xboole_0 = A_321 ),
    inference(splitRight,[status(thm)],[c_1394])).

tff(c_10043,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10015,c_250])).

tff(c_10164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_10043])).

tff(c_10165,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10327,plain,(
    ! [A_889,B_890] :
      ( r2_hidden('#skF_1'(A_889,B_890),A_889)
      | r1_tarski(A_889,B_890) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10351,plain,(
    ! [A_889] : r1_tarski(A_889,A_889) ),
    inference(resolution,[status(thm)],[c_10327,c_6])).

tff(c_48,plain,(
    ! [A_24,C_26,B_25] :
      ( r1_tarski(k2_zfmisc_1(A_24,C_26),k2_zfmisc_1(B_25,C_26))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10352,plain,(
    ! [A_891] : r1_tarski(A_891,A_891) ),
    inference(resolution,[status(thm)],[c_10327,c_6])).

tff(c_10356,plain,(
    ! [A_891] : k4_xboole_0(A_891,A_891) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10352,c_30])).

tff(c_10260,plain,(
    ! [A_886,B_887] : k4_xboole_0(A_886,k4_xboole_0(A_886,B_887)) = k3_xboole_0(A_886,B_887) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10287,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_10260])).

tff(c_10386,plain,(
    ! [A_893] : k3_xboole_0(A_893,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10356,c_10287])).

tff(c_10404,plain,(
    ! [B_2] : k3_xboole_0(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10386])).

tff(c_40,plain,(
    ! [B_20] : k2_zfmisc_1(k1_xboole_0,B_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10570,plain,(
    ! [A_911,C_912,B_913] :
      ( r1_tarski(k2_zfmisc_1(A_911,C_912),k2_zfmisc_1(B_913,C_912))
      | ~ r1_tarski(A_911,B_913) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10642,plain,(
    ! [A_916,B_917] :
      ( r1_tarski(k2_zfmisc_1(A_916,B_917),k1_xboole_0)
      | ~ r1_tarski(A_916,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_10570])).

tff(c_10645,plain,(
    ! [A_916,B_917] :
      ( k4_xboole_0(k2_zfmisc_1(A_916,B_917),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_916,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10642,c_30])).

tff(c_10657,plain,(
    ! [A_918,B_919] :
      ( k2_zfmisc_1(A_918,B_919) = k1_xboole_0
      | ~ r1_tarski(A_918,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10645])).

tff(c_10668,plain,(
    ! [A_14,B_919] :
      ( k2_zfmisc_1(A_14,B_919) = k1_xboole_0
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_10657])).

tff(c_10678,plain,(
    ! [A_920,B_921] :
      ( k2_zfmisc_1(A_920,B_921) = k1_xboole_0
      | k1_xboole_0 != A_920 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10668])).

tff(c_10205,plain,(
    ! [A_871,B_872] :
      ( k4_xboole_0(A_871,B_872) = k1_xboole_0
      | ~ r1_tarski(A_871,B_872) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10215,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_10205])).

tff(c_10281,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k4_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10215,c_10260])).

tff(c_10290,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10281])).

tff(c_10693,plain,
    ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5')
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_10678,c_10290])).

tff(c_10727,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10404,c_10693])).

tff(c_10728,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_10727])).

tff(c_10166,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10217,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10166,c_10205])).

tff(c_10284,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10217,c_10260])).

tff(c_10291,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10284])).

tff(c_11519,plain,(
    ! [A_961,C_962,B_963,D_964] : k3_xboole_0(k2_zfmisc_1(A_961,C_962),k2_zfmisc_1(B_963,D_964)) = k2_zfmisc_1(k3_xboole_0(A_961,B_963),k3_xboole_0(C_962,D_964)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_11589,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10290,c_11519])).

tff(c_11610,plain,(
    k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10291,c_11589])).

tff(c_42,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ r1_tarski(k2_zfmisc_1(A_21,B_22),k2_zfmisc_1(A_21,C_23))
      | r1_tarski(B_22,C_23)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11632,plain,(
    ! [C_23] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4',C_23))
      | r1_tarski(k3_xboole_0('#skF_5','#skF_7'),C_23)
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11610,c_42])).

tff(c_12128,plain,(
    ! [C_984] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4',C_984))
      | r1_tarski(k3_xboole_0('#skF_5','#skF_7'),C_984) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10728,c_11632])).

tff(c_12164,plain,
    ( r1_tarski(k3_xboole_0('#skF_5','#skF_7'),'#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_12128])).

tff(c_12182,plain,(
    r1_tarski(k3_xboole_0('#skF_5','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10351,c_12164])).

tff(c_12200,plain,(
    k4_xboole_0(k3_xboole_0('#skF_5','#skF_7'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12182,c_30])).

tff(c_12214,plain,(
    k4_xboole_0(k3_xboole_0('#skF_5','#skF_7'),k1_xboole_0) = k3_xboole_0(k3_xboole_0('#skF_5','#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12200,c_34])).

tff(c_12238,plain,(
    k3_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_7')) = k3_xboole_0('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32,c_12214])).

tff(c_11635,plain,(
    ! [B_22] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_22),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_22,k3_xboole_0('#skF_5','#skF_7'))
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11610,c_42])).

tff(c_12504,plain,(
    ! [B_996] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_996),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_996,k3_xboole_0('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10728,c_11635])).

tff(c_12540,plain,
    ( r1_tarski('#skF_5',k3_xboole_0('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_12504])).

tff(c_12562,plain,(
    r1_tarski('#skF_5',k3_xboole_0('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10351,c_12540])).

tff(c_12580,plain,(
    k4_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12562,c_30])).

tff(c_12593,plain,(
    k3_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_7')) = k4_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12580,c_34])).

tff(c_12617,plain,(
    k3_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12238,c_32,c_12593])).

tff(c_10490,plain,(
    ! [D_902,A_903,B_904] :
      ( r2_hidden(D_902,A_903)
      | ~ r2_hidden(D_902,k3_xboole_0(A_903,B_904)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10260,c_14])).

tff(c_10512,plain,(
    ! [D_902,B_2,A_1] :
      ( r2_hidden(D_902,B_2)
      | ~ r2_hidden(D_902,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10490])).

tff(c_12678,plain,(
    ! [D_997] :
      ( r2_hidden(D_997,'#skF_7')
      | ~ r2_hidden(D_997,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12617,c_10512])).

tff(c_12721,plain,(
    ! [A_1001] :
      ( r1_tarski(A_1001,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_1001,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12678,c_6])).

tff(c_12725,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_12721])).

tff(c_12729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10165,c_10165,c_12725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:52:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.46/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/2.69  
% 7.46/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.46/2.69  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.46/2.69  
% 7.46/2.69  %Foreground sorts:
% 7.46/2.69  
% 7.46/2.69  
% 7.46/2.69  %Background operators:
% 7.46/2.69  
% 7.46/2.69  
% 7.46/2.69  %Foreground operators:
% 7.46/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.46/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.46/2.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.46/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.46/2.69  tff('#skF_7', type, '#skF_7': $i).
% 7.46/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.46/2.69  tff('#skF_5', type, '#skF_5': $i).
% 7.46/2.69  tff('#skF_6', type, '#skF_6': $i).
% 7.46/2.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.46/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.46/2.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.46/2.69  tff('#skF_4', type, '#skF_4': $i).
% 7.46/2.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.46/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.46/2.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.46/2.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.46/2.69  
% 7.61/2.71  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 7.61/2.71  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.61/2.71  tff(f_50, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.61/2.71  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.61/2.71  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.61/2.71  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.61/2.71  tff(f_75, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 7.61/2.71  tff(f_69, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 7.61/2.71  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.61/2.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.61/2.71  tff(f_77, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 7.61/2.71  tff(c_54, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.61/2.71  tff(c_122, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | k4_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.61/2.71  tff(c_52, plain, (~r1_tarski('#skF_5', '#skF_7') | ~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.61/2.71  tff(c_88, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_52])).
% 7.61/2.71  tff(c_126, plain, (k4_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_88])).
% 7.61/2.71  tff(c_32, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.61/2.71  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.61/2.71  tff(c_157, plain, (![A_52, B_53]: (r2_hidden('#skF_1'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.61/2.71  tff(c_137, plain, (![D_42, B_43, A_44]: (~r2_hidden(D_42, B_43) | ~r2_hidden(D_42, k4_xboole_0(A_44, B_43)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.61/2.71  tff(c_140, plain, (![D_42, A_16]: (~r2_hidden(D_42, k1_xboole_0) | ~r2_hidden(D_42, A_16))), inference(superposition, [status(thm), theory('equality')], [c_32, c_137])).
% 7.61/2.71  tff(c_364, plain, (![B_69, A_70]: (~r2_hidden('#skF_1'(k1_xboole_0, B_69), A_70) | r1_tarski(k1_xboole_0, B_69))), inference(resolution, [status(thm)], [c_157, c_140])).
% 7.61/2.71  tff(c_369, plain, (![B_4]: (r1_tarski(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_8, c_364])).
% 7.61/2.71  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.61/2.71  tff(c_38, plain, (![A_19]: (k2_zfmisc_1(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.61/2.71  tff(c_442, plain, (![C_76, A_77, B_78]: (r1_tarski(k2_zfmisc_1(C_76, A_77), k2_zfmisc_1(C_76, B_78)) | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.61/2.71  tff(c_463, plain, (![A_79, A_80]: (r1_tarski(k2_zfmisc_1(A_79, A_80), k1_xboole_0) | ~r1_tarski(A_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_442])).
% 7.61/2.71  tff(c_30, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.61/2.71  tff(c_466, plain, (![A_79, A_80]: (k4_xboole_0(k2_zfmisc_1(A_79, A_80), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_463, c_30])).
% 7.61/2.71  tff(c_478, plain, (![A_81, A_82]: (k2_zfmisc_1(A_81, A_82)=k1_xboole_0 | ~r1_tarski(A_82, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_466])).
% 7.61/2.71  tff(c_489, plain, (![A_81, A_14]: (k2_zfmisc_1(A_81, A_14)=k1_xboole_0 | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_478])).
% 7.61/2.71  tff(c_496, plain, (![A_81, A_14]: (k2_zfmisc_1(A_81, A_14)=k1_xboole_0 | k1_xboole_0!=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_489])).
% 7.61/2.71  tff(c_1329, plain, (![A_121, B_122, C_123]: (~r1_tarski(k2_zfmisc_1(A_121, B_122), k2_zfmisc_1(A_121, C_123)) | r1_tarski(B_122, C_123) | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.61/2.71  tff(c_1366, plain, (![A_81, C_123, A_14]: (~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_81, C_123)) | r1_tarski(A_14, C_123) | k1_xboole_0=A_81 | k1_xboole_0!=A_14)), inference(superposition, [status(thm), theory('equality')], [c_496, c_1329])).
% 7.61/2.71  tff(c_1394, plain, (![A_14, C_123, A_81]: (r1_tarski(A_14, C_123) | k1_xboole_0=A_81 | k1_xboole_0!=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_369, c_1366])).
% 7.61/2.71  tff(c_1402, plain, (![A_124, C_125]: (r1_tarski(A_124, C_125) | k1_xboole_0!=A_124)), inference(splitLeft, [status(thm)], [c_1394])).
% 7.61/2.71  tff(c_1428, plain, (![A_126, C_127]: (k4_xboole_0(A_126, C_127)=k1_xboole_0 | k1_xboole_0!=A_126)), inference(resolution, [status(thm)], [c_1402, c_30])).
% 7.61/2.71  tff(c_34, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.61/2.71  tff(c_1448, plain, (![A_126, C_127]: (k4_xboole_0(A_126, k1_xboole_0)=k3_xboole_0(A_126, C_127) | k1_xboole_0!=A_126)), inference(superposition, [status(thm), theory('equality')], [c_1428, c_34])).
% 7.61/2.71  tff(c_1614, plain, (![C_127]: (k3_xboole_0(k1_xboole_0, C_127)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1448])).
% 7.61/2.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.61/2.71  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.61/2.71  tff(c_7990, plain, (![A_286, B_287, B_288]: (r2_hidden('#skF_1'(k4_xboole_0(A_286, B_287), B_288), A_286) | r1_tarski(k4_xboole_0(A_286, B_287), B_288))), inference(resolution, [status(thm)], [c_157, c_14])).
% 7.61/2.71  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.61/2.71  tff(c_8082, plain, (![A_289, B_290]: (r1_tarski(k4_xboole_0(A_289, B_290), A_289))), inference(resolution, [status(thm)], [c_7990, c_6])).
% 7.61/2.71  tff(c_8169, plain, (![A_289, B_290]: (k4_xboole_0(k4_xboole_0(A_289, B_290), A_289)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8082, c_30])).
% 7.61/2.71  tff(c_8144, plain, (![A_17, B_18]: (r1_tarski(k3_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_34, c_8082])).
% 7.61/2.71  tff(c_458, plain, (![C_76, A_77, B_78]: (k4_xboole_0(k2_zfmisc_1(C_76, A_77), k2_zfmisc_1(C_76, B_78))=k1_xboole_0 | ~r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_442, c_30])).
% 7.61/2.71  tff(c_2064, plain, (![A_142, C_143, B_144, D_145]: (k3_xboole_0(k2_zfmisc_1(A_142, C_143), k2_zfmisc_1(B_144, D_145))=k2_zfmisc_1(k3_xboole_0(A_142, B_144), k3_xboole_0(C_143, D_145)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.61/2.71  tff(c_56, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.61/2.71  tff(c_127, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.61/2.71  tff(c_134, plain, (k4_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_127])).
% 7.61/2.71  tff(c_220, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.61/2.71  tff(c_241, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k4_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_134, c_220])).
% 7.61/2.71  tff(c_250, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_241])).
% 7.61/2.71  tff(c_2085, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2064, c_250])).
% 7.61/2.71  tff(c_5716, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_xboole_0('#skF_5', '#skF_7')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2085, c_496])).
% 7.61/2.71  tff(c_5764, plain, (k3_xboole_0('#skF_5', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_5716])).
% 7.61/2.71  tff(c_1750, plain, (![B_135, A_136, C_137]: (~r1_tarski(k2_zfmisc_1(B_135, A_136), k2_zfmisc_1(C_137, A_136)) | r1_tarski(B_135, C_137) | k1_xboole_0=A_136)), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.61/2.71  tff(c_9445, plain, (![B_314, C_315, A_316]: (r1_tarski(B_314, C_315) | k1_xboole_0=A_316 | k4_xboole_0(k2_zfmisc_1(B_314, A_316), k2_zfmisc_1(C_315, A_316))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_1750])).
% 7.61/2.71  tff(c_9472, plain, (![B_314]: (r1_tarski(B_314, k3_xboole_0('#skF_4', '#skF_6')) | k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0 | k4_xboole_0(k2_zfmisc_1(B_314, k3_xboole_0('#skF_5', '#skF_7')), k2_zfmisc_1('#skF_4', '#skF_5'))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2085, c_9445])).
% 7.61/2.71  tff(c_9709, plain, (![B_320]: (r1_tarski(B_320, k3_xboole_0('#skF_4', '#skF_6')) | k4_xboole_0(k2_zfmisc_1(B_320, k3_xboole_0('#skF_5', '#skF_7')), k2_zfmisc_1('#skF_4', '#skF_5'))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_5764, c_9472])).
% 7.61/2.71  tff(c_9721, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_458, c_9709])).
% 7.61/2.71  tff(c_9786, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8144, c_9721])).
% 7.61/2.71  tff(c_9842, plain, (k4_xboole_0('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_9786, c_30])).
% 7.61/2.71  tff(c_235, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k3_xboole_0(A_17, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_220])).
% 7.61/2.71  tff(c_9875, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9842, c_235])).
% 7.61/2.71  tff(c_1117, plain, (![A_112, B_113]: (k4_xboole_0(A_112, k3_xboole_0(A_112, B_113))=k3_xboole_0(A_112, k4_xboole_0(A_112, B_113)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_220])).
% 7.61/2.71  tff(c_1158, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k3_xboole_0(A_1, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1117])).
% 7.61/2.71  tff(c_9970, plain, (k3_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), k4_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), '#skF_4'))=k4_xboole_0(k4_xboole_0('#skF_4', '#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9875, c_1158])).
% 7.61/2.71  tff(c_10011, plain, (k4_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1614, c_2, c_8169, c_32, c_9970])).
% 7.61/2.71  tff(c_10013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_10011])).
% 7.61/2.71  tff(c_10015, plain, (![A_321]: (k1_xboole_0=A_321)), inference(splitRight, [status(thm)], [c_1394])).
% 7.61/2.71  tff(c_10043, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10015, c_250])).
% 7.61/2.71  tff(c_10164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_10043])).
% 7.61/2.71  tff(c_10165, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 7.61/2.71  tff(c_10327, plain, (![A_889, B_890]: (r2_hidden('#skF_1'(A_889, B_890), A_889) | r1_tarski(A_889, B_890))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.61/2.71  tff(c_10351, plain, (![A_889]: (r1_tarski(A_889, A_889))), inference(resolution, [status(thm)], [c_10327, c_6])).
% 7.61/2.71  tff(c_48, plain, (![A_24, C_26, B_25]: (r1_tarski(k2_zfmisc_1(A_24, C_26), k2_zfmisc_1(B_25, C_26)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.61/2.71  tff(c_10352, plain, (![A_891]: (r1_tarski(A_891, A_891))), inference(resolution, [status(thm)], [c_10327, c_6])).
% 7.61/2.71  tff(c_10356, plain, (![A_891]: (k4_xboole_0(A_891, A_891)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10352, c_30])).
% 7.61/2.71  tff(c_10260, plain, (![A_886, B_887]: (k4_xboole_0(A_886, k4_xboole_0(A_886, B_887))=k3_xboole_0(A_886, B_887))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.61/2.71  tff(c_10287, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_10260])).
% 7.61/2.71  tff(c_10386, plain, (![A_893]: (k3_xboole_0(A_893, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10356, c_10287])).
% 7.61/2.71  tff(c_10404, plain, (![B_2]: (k3_xboole_0(k1_xboole_0, B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_10386])).
% 7.61/2.71  tff(c_40, plain, (![B_20]: (k2_zfmisc_1(k1_xboole_0, B_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.61/2.71  tff(c_10570, plain, (![A_911, C_912, B_913]: (r1_tarski(k2_zfmisc_1(A_911, C_912), k2_zfmisc_1(B_913, C_912)) | ~r1_tarski(A_911, B_913))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.61/2.71  tff(c_10642, plain, (![A_916, B_917]: (r1_tarski(k2_zfmisc_1(A_916, B_917), k1_xboole_0) | ~r1_tarski(A_916, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_10570])).
% 7.61/2.71  tff(c_10645, plain, (![A_916, B_917]: (k4_xboole_0(k2_zfmisc_1(A_916, B_917), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_916, k1_xboole_0))), inference(resolution, [status(thm)], [c_10642, c_30])).
% 7.61/2.71  tff(c_10657, plain, (![A_918, B_919]: (k2_zfmisc_1(A_918, B_919)=k1_xboole_0 | ~r1_tarski(A_918, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10645])).
% 7.61/2.71  tff(c_10668, plain, (![A_14, B_919]: (k2_zfmisc_1(A_14, B_919)=k1_xboole_0 | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_10657])).
% 7.61/2.71  tff(c_10678, plain, (![A_920, B_921]: (k2_zfmisc_1(A_920, B_921)=k1_xboole_0 | k1_xboole_0!=A_920)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10668])).
% 7.61/2.71  tff(c_10205, plain, (![A_871, B_872]: (k4_xboole_0(A_871, B_872)=k1_xboole_0 | ~r1_tarski(A_871, B_872))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.61/2.71  tff(c_10215, plain, (k4_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_10205])).
% 7.61/2.71  tff(c_10281, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k4_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10215, c_10260])).
% 7.61/2.71  tff(c_10290, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10281])).
% 7.61/2.71  tff(c_10693, plain, (k3_xboole_0(k1_xboole_0, k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5') | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_10678, c_10290])).
% 7.61/2.71  tff(c_10727, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10404, c_10693])).
% 7.61/2.71  tff(c_10728, plain, (k1_xboole_0!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_10727])).
% 7.61/2.71  tff(c_10166, plain, (r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 7.61/2.71  tff(c_10217, plain, (k4_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_10166, c_10205])).
% 7.61/2.71  tff(c_10284, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10217, c_10260])).
% 7.61/2.71  tff(c_10291, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10284])).
% 7.61/2.71  tff(c_11519, plain, (![A_961, C_962, B_963, D_964]: (k3_xboole_0(k2_zfmisc_1(A_961, C_962), k2_zfmisc_1(B_963, D_964))=k2_zfmisc_1(k3_xboole_0(A_961, B_963), k3_xboole_0(C_962, D_964)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.61/2.71  tff(c_11589, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10290, c_11519])).
% 7.61/2.71  tff(c_11610, plain, (k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10291, c_11589])).
% 7.61/2.71  tff(c_42, plain, (![A_21, B_22, C_23]: (~r1_tarski(k2_zfmisc_1(A_21, B_22), k2_zfmisc_1(A_21, C_23)) | r1_tarski(B_22, C_23) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.61/2.71  tff(c_11632, plain, (![C_23]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', C_23)) | r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), C_23) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11610, c_42])).
% 7.61/2.71  tff(c_12128, plain, (![C_984]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', C_984)) | r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), C_984))), inference(negUnitSimplification, [status(thm)], [c_10728, c_11632])).
% 7.61/2.71  tff(c_12164, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_12128])).
% 7.61/2.71  tff(c_12182, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10351, c_12164])).
% 7.61/2.71  tff(c_12200, plain, (k4_xboole_0(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_12182, c_30])).
% 7.61/2.71  tff(c_12214, plain, (k4_xboole_0(k3_xboole_0('#skF_5', '#skF_7'), k1_xboole_0)=k3_xboole_0(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12200, c_34])).
% 7.61/2.71  tff(c_12238, plain, (k3_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))=k3_xboole_0('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32, c_12214])).
% 7.61/2.71  tff(c_11635, plain, (![B_22]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_22), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_22, k3_xboole_0('#skF_5', '#skF_7')) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11610, c_42])).
% 7.61/2.71  tff(c_12504, plain, (![B_996]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_996), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_996, k3_xboole_0('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_10728, c_11635])).
% 7.61/2.71  tff(c_12540, plain, (r1_tarski('#skF_5', k3_xboole_0('#skF_5', '#skF_7')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_12504])).
% 7.61/2.71  tff(c_12562, plain, (r1_tarski('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_10351, c_12540])).
% 7.61/2.71  tff(c_12580, plain, (k4_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_12562, c_30])).
% 7.61/2.71  tff(c_12593, plain, (k3_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))=k4_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12580, c_34])).
% 7.61/2.71  tff(c_12617, plain, (k3_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_12238, c_32, c_12593])).
% 7.61/2.71  tff(c_10490, plain, (![D_902, A_903, B_904]: (r2_hidden(D_902, A_903) | ~r2_hidden(D_902, k3_xboole_0(A_903, B_904)))), inference(superposition, [status(thm), theory('equality')], [c_10260, c_14])).
% 7.61/2.71  tff(c_10512, plain, (![D_902, B_2, A_1]: (r2_hidden(D_902, B_2) | ~r2_hidden(D_902, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10490])).
% 7.61/2.71  tff(c_12678, plain, (![D_997]: (r2_hidden(D_997, '#skF_7') | ~r2_hidden(D_997, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12617, c_10512])).
% 7.61/2.71  tff(c_12721, plain, (![A_1001]: (r1_tarski(A_1001, '#skF_7') | ~r2_hidden('#skF_1'(A_1001, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_12678, c_6])).
% 7.61/2.71  tff(c_12725, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_8, c_12721])).
% 7.61/2.71  tff(c_12729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10165, c_10165, c_12725])).
% 7.61/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.61/2.71  
% 7.61/2.71  Inference rules
% 7.61/2.71  ----------------------
% 7.61/2.71  #Ref     : 2
% 7.61/2.71  #Sup     : 3191
% 7.61/2.71  #Fact    : 0
% 7.61/2.71  #Define  : 0
% 7.61/2.71  #Split   : 10
% 7.61/2.71  #Chain   : 0
% 7.61/2.71  #Close   : 0
% 7.61/2.71  
% 7.61/2.71  Ordering : KBO
% 7.61/2.71  
% 7.61/2.71  Simplification rules
% 7.61/2.71  ----------------------
% 7.61/2.71  #Subsume      : 870
% 7.61/2.71  #Demod        : 1456
% 7.61/2.71  #Tautology    : 1528
% 7.61/2.71  #SimpNegUnit  : 114
% 7.61/2.71  #BackRed      : 21
% 7.61/2.71  
% 7.61/2.71  #Partial instantiations: 148
% 7.61/2.71  #Strategies tried      : 1
% 7.61/2.71  
% 7.61/2.71  Timing (in seconds)
% 7.61/2.71  ----------------------
% 7.61/2.72  Preprocessing        : 0.34
% 7.61/2.72  Parsing              : 0.18
% 7.61/2.72  CNF conversion       : 0.03
% 7.61/2.72  Main loop            : 1.53
% 7.61/2.72  Inferencing          : 0.43
% 7.61/2.72  Reduction            : 0.59
% 7.61/2.72  Demodulation         : 0.45
% 7.61/2.72  BG Simplification    : 0.05
% 7.61/2.72  Subsumption          : 0.35
% 7.61/2.72  Abstraction          : 0.07
% 7.61/2.72  MUC search           : 0.00
% 7.61/2.72  Cooper               : 0.00
% 7.61/2.72  Total                : 1.92
% 7.61/2.72  Index Insertion      : 0.00
% 7.61/2.72  Index Deletion       : 0.00
% 7.61/2.72  Index Matching       : 0.00
% 7.61/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
