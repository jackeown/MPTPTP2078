%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0277+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:02 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 610 expanded)
%              Number of leaves         :   18 ( 174 expanded)
%              Depth                    :    9
%              Number of atoms          :  236 (1618 expanded)
%              Number of equality atoms :  196 (1499 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_30,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_81,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_105,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_22,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_104,plain,(
    k1_tarski('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_18,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_106,plain,(
    k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_36,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_134,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    ! [B_26,C_27,A_28] :
      ( k2_tarski(B_26,C_27) = A_28
      | k1_tarski(C_27) = A_28
      | k1_tarski(B_26) = A_28
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k2_tarski(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_139,plain,(
    ! [B_29,C_30,A_31] :
      ( k2_tarski(B_29,C_30) = A_31
      | k1_tarski(C_30) = A_31
      | k1_tarski(B_29) = A_31
      | k1_xboole_0 = A_31
      | k4_xboole_0(A_31,k2_tarski(B_29,C_30)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_108])).

tff(c_142,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_139])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_105,c_104,c_106,c_142])).

tff(c_159,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_161,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_34,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_107,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_162,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_107])).

tff(c_6,plain,(
    ! [B_2,C_3] : r1_tarski(k2_tarski(B_2,C_3),k2_tarski(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    ! [B_2,C_3] : k4_xboole_0(k2_tarski(B_2,C_3),k2_tarski(B_2,C_3)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_46])).

tff(c_169,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_63])).

tff(c_198,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_169])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_198])).

tff(c_221,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_223,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_12,plain,(
    ! [B_2,C_3] : r1_tarski(k1_xboole_0,k2_tarski(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [B_2,C_3] : k4_xboole_0(k1_xboole_0,k2_tarski(B_2,C_3)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_46])).

tff(c_231,plain,(
    ! [B_2,C_3] : k4_xboole_0('#skF_1',k2_tarski(B_2,C_3)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_223,c_66])).

tff(c_226,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_107])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_226])).

tff(c_248,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_250,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_8,plain,(
    ! [C_3,B_2] : r1_tarski(k1_tarski(C_3),k2_tarski(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_267,plain,(
    ! [B_34] : r1_tarski('#skF_1',k2_tarski(B_34,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_8])).

tff(c_16,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k1_xboole_0
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_277,plain,(
    ! [B_34] : k4_xboole_0('#skF_1',k2_tarski(B_34,'#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_267,c_16])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_107])).

tff(c_292,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_10,plain,(
    ! [B_2,C_3] : r1_tarski(k1_tarski(B_2),k2_tarski(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_65,plain,(
    ! [B_2,C_3] : k4_xboole_0(k1_tarski(B_2),k2_tarski(B_2,C_3)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_46])).

tff(c_297,plain,(
    ! [C_3] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_3)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_65])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_107])).

tff(c_342,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_352,plain,(
    ! [B_39,C_40,A_41] :
      ( k2_tarski(B_39,C_40) = A_41
      | k1_tarski(C_40) = A_41
      | k1_tarski(B_39) = A_41
      | k1_xboole_0 = A_41
      | ~ r1_tarski(A_41,k2_tarski(B_39,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_379,plain,(
    ! [B_42,C_43,A_44] :
      ( k2_tarski(B_42,C_43) = A_44
      | k1_tarski(C_43) = A_44
      | k1_tarski(B_42) = A_44
      | k1_xboole_0 = A_44
      | k4_xboole_0(A_44,k2_tarski(B_42,C_43)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_352])).

tff(c_385,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_379])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_105,c_104,c_106,c_385])).

tff(c_403,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_404,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_20,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_481,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_20])).

tff(c_482,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_481])).

tff(c_493,plain,(
    ! [B_2,C_3] : k4_xboole_0('#skF_1',k2_tarski(B_2,C_3)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_482,c_66])).

tff(c_405,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_487,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_405])).

tff(c_529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_487])).

tff(c_530,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_481])).

tff(c_532,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_530])).

tff(c_533,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_405])).

tff(c_537,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_63])).

tff(c_565,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_537])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_565])).

tff(c_590,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_592,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_596,plain,(
    ! [C_3] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_3)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_592,c_65])).

tff(c_623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_405])).

tff(c_624,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_64,plain,(
    ! [C_3,B_2] : k4_xboole_0(k1_tarski(C_3),k2_tarski(B_2,C_3)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_632,plain,(
    ! [B_2] : k4_xboole_0('#skF_1',k2_tarski(B_2,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_64])).

tff(c_703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_405])).

tff(c_705,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_705])).

tff(c_781,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_835,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_28])).

tff(c_836,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_835])).

tff(c_844,plain,(
    ! [B_2,C_3] : k4_xboole_0('#skF_1',k2_tarski(B_2,C_3)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_836,c_66])).

tff(c_780,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_839,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_780])).

tff(c_861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_839])).

tff(c_862,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_835])).

tff(c_864,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_862])).

tff(c_866,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_780])).

tff(c_873,plain,(
    k4_xboole_0(k2_tarski('#skF_2','#skF_3'),'#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_864,c_63])).

tff(c_899,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_873])).

tff(c_922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_866,c_899])).

tff(c_923,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_862])).

tff(c_926,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_923])).

tff(c_930,plain,(
    ! [C_3] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_3)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_65])).

tff(c_964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_780])).

tff(c_965,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_923])).

tff(c_973,plain,(
    ! [B_2] : k4_xboole_0('#skF_1',k2_tarski(B_2,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_965,c_64])).

tff(c_997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_780])).

tff(c_999,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_24,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1052,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_24])).

tff(c_1053,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1052])).

tff(c_1061,plain,(
    ! [B_2,C_3] : k4_xboole_0('#skF_1',k2_tarski(B_2,C_3)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_1053,c_66])).

tff(c_998,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1056,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_998])).

tff(c_1078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1056])).

tff(c_1079,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1052])).

tff(c_1081,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1079])).

tff(c_1082,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_998])).

tff(c_1086,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_63])).

tff(c_1114,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_1086])).

tff(c_1145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1082,c_1114])).

tff(c_1146,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1079])).

tff(c_1150,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1146])).

tff(c_1154,plain,(
    ! [C_3] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_3)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1150,c_65])).

tff(c_1188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1154,c_998])).

tff(c_1189,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1146])).

tff(c_1197,plain,(
    ! [B_2] : k4_xboole_0('#skF_1',k2_tarski(B_2,'#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1189,c_64])).

tff(c_1221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_998])).

tff(c_1223,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1225,plain,(
    ! [B_2,C_3] : k4_xboole_0('#skF_4',k2_tarski(B_2,C_3)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_1223,c_66])).

tff(c_32,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1307,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_1223,c_32])).

tff(c_1308,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1307])).

tff(c_1222,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1239,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_1222])).

tff(c_1309,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1308,c_1239])).

tff(c_1312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1225,c_1309])).

tff(c_1313,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1307])).

tff(c_1315,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1313])).

tff(c_1316,plain,(
    k4_xboole_0('#skF_1','#skF_1') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1315,c_1239])).

tff(c_1336,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_6])).

tff(c_1350,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1315,c_1336])).

tff(c_1226,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = '#skF_4'
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_16])).

tff(c_1360,plain,(
    k4_xboole_0('#skF_1','#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1350,c_1226])).

tff(c_1372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1316,c_1360])).

tff(c_1373,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1313])).

tff(c_1375,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1373])).

tff(c_1397,plain,(
    ! [C_94] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_10])).

tff(c_1401,plain,(
    ! [C_94] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_94)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1397,c_1226])).

tff(c_1414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1239])).

tff(c_1415,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1373])).

tff(c_1435,plain,(
    ! [B_96] : r1_tarski('#skF_1',k2_tarski(B_96,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1415,c_8])).

tff(c_1439,plain,(
    ! [B_96] : k4_xboole_0('#skF_1',k2_tarski(B_96,'#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1435,c_1226])).

tff(c_1447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1239])).

%------------------------------------------------------------------------------
