%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:20 EST 2020

% Result     : Theorem 6.16s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :  186 (1382 expanded)
%              Number of leaves         :   26 ( 456 expanded)
%              Depth                    :   13
%              Number of atoms          :  292 (2313 expanded)
%              Number of equality atoms :  214 (1939 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(A_39,B_40)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_134,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_121])).

tff(c_24,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4737,plain,(
    ! [A_251,C_252,B_253] :
      ( r1_tarski(A_251,C_252)
      | ~ r1_tarski(B_253,C_252)
      | ~ r1_tarski(A_251,B_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4759,plain,(
    ! [A_254,A_255] :
      ( r1_tarski(A_254,A_255)
      | ~ r1_tarski(A_254,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_4737])).

tff(c_4762,plain,(
    ! [A_13,A_255] :
      ( r1_tarski(A_13,A_255)
      | k4_xboole_0(A_13,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_4759])).

tff(c_4777,plain,(
    ! [A_256,A_257] :
      ( r1_tarski(A_256,A_257)
      | k1_xboole_0 != A_256 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4762])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4799,plain,(
    ! [A_258,A_259] :
      ( k4_xboole_0(A_258,A_259) = k1_xboole_0
      | k1_xboole_0 != A_258 ) ),
    inference(resolution,[status(thm)],[c_4777,c_22])).

tff(c_3661,plain,(
    ! [A_200,C_201,B_202] :
      ( r1_tarski(A_200,C_201)
      | ~ r1_tarski(B_202,C_201)
      | ~ r1_tarski(A_200,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3731,plain,(
    ! [A_205,A_206] :
      ( r1_tarski(A_205,A_206)
      | ~ r1_tarski(A_205,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_3661])).

tff(c_3734,plain,(
    ! [A_13,A_206] :
      ( r1_tarski(A_13,A_206)
      | k4_xboole_0(A_13,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_3731])).

tff(c_3749,plain,(
    ! [A_207,A_208] :
      ( r1_tarski(A_207,A_208)
      | k1_xboole_0 != A_207 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3734])).

tff(c_3831,plain,(
    ! [A_212,A_213] :
      ( k4_xboole_0(A_212,A_213) = k1_xboole_0
      | k1_xboole_0 != A_212 ) ),
    inference(resolution,[status(thm)],[c_3749,c_22])).

tff(c_490,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(A_63,C_64)
      | ~ r1_tarski(B_65,C_64)
      | ~ r1_tarski(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_506,plain,(
    ! [A_66,A_67] :
      ( r1_tarski(A_66,A_67)
      | ~ r1_tarski(A_66,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_490])).

tff(c_509,plain,(
    ! [A_13,A_67] :
      ( r1_tarski(A_13,A_67)
      | k4_xboole_0(A_13,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_506])).

tff(c_524,plain,(
    ! [A_68,A_69] :
      ( r1_tarski(A_68,A_69)
      | k1_xboole_0 != A_68 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_509])).

tff(c_543,plain,(
    ! [A_68,A_69] :
      ( k4_xboole_0(A_68,A_69) = k1_xboole_0
      | k1_xboole_0 != A_68 ) ),
    inference(resolution,[status(thm)],[c_524,c_22])).

tff(c_56,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_154,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_48,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_300,plain,(
    k1_tarski('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_206,plain,(
    ! [A_48,B_49] : k2_xboole_0(k1_tarski(A_48),k1_tarski(B_49)) = k2_tarski(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_371,plain,(
    ! [B_59,A_60] : k2_xboole_0(k1_tarski(B_59),k1_tarski(A_60)) = k2_tarski(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2])).

tff(c_32,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),k1_tarski(B_25)) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_377,plain,(
    ! [B_59,A_60] : k2_tarski(B_59,A_60) = k2_tarski(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_32])).

tff(c_52,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_485,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_52])).

tff(c_486,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_44,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_603,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0
    | k2_tarski('#skF_6','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_377,c_44])).

tff(c_604,plain,(
    k2_tarski('#skF_6','#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_603])).

tff(c_522,plain,(
    ! [A_67] : r1_tarski(k1_xboole_0,A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_509])).

tff(c_60,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_817,plain,
    ( k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0
    | k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_377,c_60])).

tff(c_818,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_817])).

tff(c_822,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_818])).

tff(c_62,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1397,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_377,c_62])).

tff(c_1398,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_822,c_1397])).

tff(c_1399,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1398])).

tff(c_26,plain,(
    ! [A_16,B_17,C_18] :
      ( r1_tarski(A_16,k2_xboole_0(B_17,C_18))
      | ~ r1_tarski(k4_xboole_0(A_16,B_17),C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1406,plain,(
    ! [C_18] :
      ( r1_tarski('#skF_4',k2_xboole_0(k2_tarski('#skF_6','#skF_5'),C_18))
      | ~ r1_tarski(k1_xboole_0,C_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1399,c_26])).

tff(c_1442,plain,(
    ! [C_117] : r1_tarski('#skF_4',k2_xboole_0(k2_tarski('#skF_6','#skF_5'),C_117)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_1406])).

tff(c_1470,plain,(
    r1_tarski('#skF_4',k2_tarski('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1442])).

tff(c_1498,plain,(
    ! [B_118,C_119,A_120] :
      ( k2_tarski(B_118,C_119) = A_120
      | k1_tarski(C_119) = A_120
      | k1_tarski(B_118) = A_120
      | k1_xboole_0 = A_120
      | ~ r1_tarski(A_120,k2_tarski(B_118,C_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1501,plain,
    ( k2_tarski('#skF_6','#skF_5') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1470,c_1498])).

tff(c_1532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_300,c_486,c_604,c_1501])).

tff(c_1533,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1398])).

tff(c_1687,plain,(
    k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1533])).

tff(c_1688,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1687,c_818])).

tff(c_1691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_1688])).

tff(c_1692,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1533])).

tff(c_1694,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1692])).

tff(c_38,plain,(
    ! [C_28,B_27] : r1_tarski(k1_tarski(C_28),k2_tarski(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_184,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_201,plain,(
    ! [C_28,B_27] : k4_xboole_0(k1_tarski(C_28),k2_tarski(B_27,C_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_184])).

tff(c_1707,plain,(
    ! [B_27] : k4_xboole_0('#skF_1',k2_tarski(B_27,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1694,c_201])).

tff(c_1840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_818])).

tff(c_1841,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1692])).

tff(c_40,plain,(
    ! [B_27,C_28] : r1_tarski(k1_tarski(B_27),k2_tarski(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_202,plain,(
    ! [B_27,C_28] : k4_xboole_0(k1_tarski(B_27),k2_tarski(B_27,C_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_184])).

tff(c_1852,plain,(
    ! [C_28] : k4_xboole_0('#skF_1',k2_tarski('#skF_3',C_28)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1841,c_202])).

tff(c_1988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_818])).

tff(c_1989,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_817])).

tff(c_1994,plain,(
    ! [C_18] :
      ( r1_tarski('#skF_4',k2_xboole_0(k2_tarski('#skF_6','#skF_5'),C_18))
      | ~ r1_tarski(k1_xboole_0,C_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1989,c_26])).

tff(c_2495,plain,(
    ! [C_156] : r1_tarski('#skF_4',k2_xboole_0(k2_tarski('#skF_6','#skF_5'),C_156)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_1994])).

tff(c_2519,plain,(
    r1_tarski('#skF_4',k2_tarski('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2495])).

tff(c_2554,plain,(
    ! [B_157,C_158,A_159] :
      ( k2_tarski(B_157,C_158) = A_159
      | k1_tarski(C_158) = A_159
      | k1_tarski(B_157) = A_159
      | k1_xboole_0 = A_159
      | ~ r1_tarski(A_159,k2_tarski(B_157,C_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2557,plain,
    ( k2_tarski('#skF_6','#skF_5') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2519,c_2554])).

tff(c_2588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_300,c_486,c_604,c_2557])).

tff(c_2589,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_603])).

tff(c_2746,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_2589])).

tff(c_2590,plain,(
    k2_tarski('#skF_6','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_603])).

tff(c_46,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3138,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2590,c_377,c_377,c_46])).

tff(c_3139,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2746,c_3138])).

tff(c_3140,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3139])).

tff(c_3153,plain,(
    ! [B_27] : k4_xboole_0('#skF_1',k2_tarski(B_27,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3140,c_201])).

tff(c_3284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3153,c_2589])).

tff(c_3285,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3139])).

tff(c_3428,plain,(
    k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3285])).

tff(c_3429,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3428,c_2589])).

tff(c_3432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_3429])).

tff(c_3433,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3285])).

tff(c_3444,plain,(
    ! [C_28] : k4_xboole_0('#skF_1',k2_tarski('#skF_3',C_28)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3433,c_202])).

tff(c_3630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3444,c_2589])).

tff(c_3631,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_3880,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3831,c_3631])).

tff(c_3632,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_54,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4247,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3632,c_377,c_54])).

tff(c_4248,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_3880,c_4247])).

tff(c_4249,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4248])).

tff(c_4262,plain,(
    ! [B_27] : k4_xboole_0('#skF_1',k2_tarski(B_27,'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4249,c_201])).

tff(c_4369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4262,c_3631])).

tff(c_4370,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4248])).

tff(c_4375,plain,(
    k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4370])).

tff(c_4376,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4375,c_3631])).

tff(c_4379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_4376])).

tff(c_4380,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4370])).

tff(c_4393,plain,(
    ! [C_28] : k4_xboole_0('#skF_1',k2_tarski('#skF_3',C_28)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4380,c_202])).

tff(c_4527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4393,c_3631])).

tff(c_4528,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4862,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4799,c_4528])).

tff(c_4529,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_5615,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4529,c_50])).

tff(c_5616,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_4862,c_5615])).

tff(c_5617,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5616])).

tff(c_5674,plain,(
    ! [C_295] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_295)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5617,c_40])).

tff(c_5692,plain,(
    ! [C_295] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_295)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5674,c_22])).

tff(c_5699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5692,c_4528])).

tff(c_5700,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5616])).

tff(c_5702,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5700])).

tff(c_5703,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5702,c_4528])).

tff(c_5706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_5703])).

tff(c_5707,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5700])).

tff(c_5741,plain,(
    ! [B_296] : r1_tarski('#skF_1',k2_tarski(B_296,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5707,c_38])).

tff(c_5763,plain,(
    ! [B_296] : k4_xboole_0('#skF_1',k2_tarski(B_296,'#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5741,c_22])).

tff(c_5857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5763,c_4528])).

tff(c_5859,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5860,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5859,c_134])).

tff(c_5862,plain,(
    ! [A_15] : k4_xboole_0(A_15,'#skF_4') = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5859,c_24])).

tff(c_5944,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5859,c_20])).

tff(c_5863,plain,(
    ! [A_12] : r1_tarski('#skF_4',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5859,c_18])).

tff(c_6254,plain,(
    ! [A_325,C_326,B_327] :
      ( r1_tarski(A_325,C_326)
      | ~ r1_tarski(B_327,C_326)
      | ~ r1_tarski(A_325,B_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6270,plain,(
    ! [A_328,A_329] :
      ( r1_tarski(A_328,A_329)
      | ~ r1_tarski(A_328,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5863,c_6254])).

tff(c_6273,plain,(
    ! [A_13,A_329] :
      ( r1_tarski(A_13,A_329)
      | k4_xboole_0(A_13,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_5944,c_6270])).

tff(c_6288,plain,(
    ! [A_330,A_331] :
      ( r1_tarski(A_330,A_331)
      | A_330 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5862,c_6273])).

tff(c_5947,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = '#skF_4'
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5859,c_22])).

tff(c_6310,plain,(
    ! [A_332,A_333] :
      ( k4_xboole_0(A_332,A_333) = '#skF_4'
      | A_332 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_6288,c_5947])).

tff(c_6034,plain,(
    ! [A_315,B_316] : k2_xboole_0(k1_tarski(A_315),k1_tarski(B_316)) = k2_tarski(A_315,B_316) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6135,plain,(
    ! [B_321,A_322] : k2_xboole_0(k1_tarski(B_321),k1_tarski(A_322)) = k2_tarski(A_322,B_321) ),
    inference(superposition,[status(thm),theory(equality)],[c_6034,c_2])).

tff(c_6141,plain,(
    ! [B_321,A_322] : k2_tarski(B_321,A_322) = k2_tarski(A_322,B_321) ),
    inference(superposition,[status(thm),theory(equality)],[c_6135,c_32])).

tff(c_5858,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5914,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_2','#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5859,c_5858])).

tff(c_6184,plain,(
    k4_xboole_0('#skF_1',k2_tarski('#skF_3','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6141,c_5914])).

tff(c_6359,plain,(
    '#skF_1' != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6310,c_6184])).

tff(c_58,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6555,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5859,c_5859,c_6141,c_58])).

tff(c_6556,plain,
    ( k2_tarski('#skF_3','#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_6359,c_6555])).

tff(c_6557,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6556])).

tff(c_5948,plain,(
    ! [A_308,B_309] :
      ( k4_xboole_0(A_308,B_309) = '#skF_4'
      | ~ r1_tarski(A_308,B_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5859,c_22])).

tff(c_5966,plain,(
    ! [C_28,B_27] : k4_xboole_0(k1_tarski(C_28),k2_tarski(B_27,C_28)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_5948])).

tff(c_6576,plain,(
    ! [B_27] : k4_xboole_0('#skF_1',k2_tarski(B_27,'#skF_2')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6557,c_5966])).

tff(c_6751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6576,c_6184])).

tff(c_6752,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6556])).

tff(c_6807,plain,(
    k2_tarski('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_6752])).

tff(c_6808,plain,(
    k4_xboole_0('#skF_1','#skF_1') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6807,c_6184])).

tff(c_6811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5860,c_6808])).

tff(c_6812,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6752])).

tff(c_5967,plain,(
    ! [B_27,C_28] : k4_xboole_0(k1_tarski(B_27),k2_tarski(B_27,C_28)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_5948])).

tff(c_6829,plain,(
    ! [C_28] : k4_xboole_0('#skF_1',k2_tarski('#skF_3',C_28)) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6812,c_5967])).

tff(c_6982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6829,c_6184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.16/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.18  
% 6.16/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.18  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.16/2.18  
% 6.16/2.18  %Foreground sorts:
% 6.16/2.18  
% 6.16/2.18  
% 6.16/2.18  %Background operators:
% 6.16/2.18  
% 6.16/2.18  
% 6.16/2.18  %Foreground operators:
% 6.16/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.16/2.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.16/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.16/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.16/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.16/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.16/2.18  tff('#skF_5', type, '#skF_5': $i).
% 6.16/2.18  tff('#skF_6', type, '#skF_6': $i).
% 6.16/2.18  tff('#skF_2', type, '#skF_2': $i).
% 6.16/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.16/2.18  tff('#skF_1', type, '#skF_1': $i).
% 6.16/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.16/2.18  tff('#skF_4', type, '#skF_4': $i).
% 6.16/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.16/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.16/2.18  
% 6.16/2.20  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 6.16/2.20  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.16/2.20  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.16/2.20  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 6.16/2.20  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.16/2.20  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.16/2.20  tff(f_94, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 6.16/2.20  tff(f_63, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 6.16/2.20  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.16/2.20  tff(f_57, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 6.16/2.20  tff(f_78, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 6.16/2.20  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.16/2.20  tff(c_121, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(A_39, B_40))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.16/2.20  tff(c_134, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_121])).
% 6.16/2.20  tff(c_24, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.16/2.20  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.16/2.20  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.16/2.20  tff(c_4737, plain, (![A_251, C_252, B_253]: (r1_tarski(A_251, C_252) | ~r1_tarski(B_253, C_252) | ~r1_tarski(A_251, B_253))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.16/2.20  tff(c_4759, plain, (![A_254, A_255]: (r1_tarski(A_254, A_255) | ~r1_tarski(A_254, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_4737])).
% 6.16/2.20  tff(c_4762, plain, (![A_13, A_255]: (r1_tarski(A_13, A_255) | k4_xboole_0(A_13, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_4759])).
% 6.16/2.20  tff(c_4777, plain, (![A_256, A_257]: (r1_tarski(A_256, A_257) | k1_xboole_0!=A_256)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4762])).
% 6.16/2.20  tff(c_22, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k1_xboole_0 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.16/2.20  tff(c_4799, plain, (![A_258, A_259]: (k4_xboole_0(A_258, A_259)=k1_xboole_0 | k1_xboole_0!=A_258)), inference(resolution, [status(thm)], [c_4777, c_22])).
% 6.16/2.20  tff(c_3661, plain, (![A_200, C_201, B_202]: (r1_tarski(A_200, C_201) | ~r1_tarski(B_202, C_201) | ~r1_tarski(A_200, B_202))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.16/2.20  tff(c_3731, plain, (![A_205, A_206]: (r1_tarski(A_205, A_206) | ~r1_tarski(A_205, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_3661])).
% 6.16/2.20  tff(c_3734, plain, (![A_13, A_206]: (r1_tarski(A_13, A_206) | k4_xboole_0(A_13, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_3731])).
% 6.16/2.20  tff(c_3749, plain, (![A_207, A_208]: (r1_tarski(A_207, A_208) | k1_xboole_0!=A_207)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3734])).
% 6.16/2.20  tff(c_3831, plain, (![A_212, A_213]: (k4_xboole_0(A_212, A_213)=k1_xboole_0 | k1_xboole_0!=A_212)), inference(resolution, [status(thm)], [c_3749, c_22])).
% 6.16/2.20  tff(c_490, plain, (![A_63, C_64, B_65]: (r1_tarski(A_63, C_64) | ~r1_tarski(B_65, C_64) | ~r1_tarski(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.16/2.20  tff(c_506, plain, (![A_66, A_67]: (r1_tarski(A_66, A_67) | ~r1_tarski(A_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_490])).
% 6.16/2.20  tff(c_509, plain, (![A_13, A_67]: (r1_tarski(A_13, A_67) | k4_xboole_0(A_13, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_506])).
% 6.16/2.20  tff(c_524, plain, (![A_68, A_69]: (r1_tarski(A_68, A_69) | k1_xboole_0!=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_509])).
% 6.16/2.20  tff(c_543, plain, (![A_68, A_69]: (k4_xboole_0(A_68, A_69)=k1_xboole_0 | k1_xboole_0!=A_68)), inference(resolution, [status(thm)], [c_524, c_22])).
% 6.16/2.20  tff(c_56, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.20  tff(c_154, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_56])).
% 6.16/2.20  tff(c_48, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.20  tff(c_300, plain, (k1_tarski('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_48])).
% 6.16/2.20  tff(c_206, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), k1_tarski(B_49))=k2_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.16/2.20  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.16/2.20  tff(c_371, plain, (![B_59, A_60]: (k2_xboole_0(k1_tarski(B_59), k1_tarski(A_60))=k2_tarski(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_206, c_2])).
% 6.16/2.20  tff(c_32, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), k1_tarski(B_25))=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.16/2.20  tff(c_377, plain, (![B_59, A_60]: (k2_tarski(B_59, A_60)=k2_tarski(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_371, c_32])).
% 6.16/2.20  tff(c_52, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.20  tff(c_485, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0 | k1_tarski('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_377, c_52])).
% 6.16/2.20  tff(c_486, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_485])).
% 6.16/2.20  tff(c_44, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.20  tff(c_603, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0 | k2_tarski('#skF_6', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_377, c_377, c_44])).
% 6.16/2.20  tff(c_604, plain, (k2_tarski('#skF_6', '#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_603])).
% 6.16/2.20  tff(c_522, plain, (![A_67]: (r1_tarski(k1_xboole_0, A_67))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_509])).
% 6.16/2.20  tff(c_60, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0 | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.20  tff(c_817, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0 | k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_377, c_377, c_60])).
% 6.16/2.20  tff(c_818, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_817])).
% 6.16/2.20  tff(c_822, plain, (k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_543, c_818])).
% 6.16/2.20  tff(c_62, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.20  tff(c_1397, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_377, c_377, c_62])).
% 6.16/2.20  tff(c_1398, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_822, c_1397])).
% 6.16/2.20  tff(c_1399, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1398])).
% 6.16/2.20  tff(c_26, plain, (![A_16, B_17, C_18]: (r1_tarski(A_16, k2_xboole_0(B_17, C_18)) | ~r1_tarski(k4_xboole_0(A_16, B_17), C_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.16/2.20  tff(c_1406, plain, (![C_18]: (r1_tarski('#skF_4', k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), C_18)) | ~r1_tarski(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_1399, c_26])).
% 6.16/2.20  tff(c_1442, plain, (![C_117]: (r1_tarski('#skF_4', k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), C_117)))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_1406])).
% 6.16/2.20  tff(c_1470, plain, (r1_tarski('#skF_4', k2_tarski('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1442])).
% 6.16/2.20  tff(c_1498, plain, (![B_118, C_119, A_120]: (k2_tarski(B_118, C_119)=A_120 | k1_tarski(C_119)=A_120 | k1_tarski(B_118)=A_120 | k1_xboole_0=A_120 | ~r1_tarski(A_120, k2_tarski(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.16/2.20  tff(c_1501, plain, (k2_tarski('#skF_6', '#skF_5')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1470, c_1498])).
% 6.16/2.20  tff(c_1532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_300, c_486, c_604, c_1501])).
% 6.16/2.20  tff(c_1533, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1398])).
% 6.16/2.20  tff(c_1687, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_1533])).
% 6.16/2.20  tff(c_1688, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1687, c_818])).
% 6.16/2.20  tff(c_1691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_1688])).
% 6.16/2.20  tff(c_1692, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1533])).
% 6.16/2.20  tff(c_1694, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_1692])).
% 6.16/2.20  tff(c_38, plain, (![C_28, B_27]: (r1_tarski(k1_tarski(C_28), k2_tarski(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.16/2.20  tff(c_184, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.16/2.20  tff(c_201, plain, (![C_28, B_27]: (k4_xboole_0(k1_tarski(C_28), k2_tarski(B_27, C_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_184])).
% 6.16/2.20  tff(c_1707, plain, (![B_27]: (k4_xboole_0('#skF_1', k2_tarski(B_27, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1694, c_201])).
% 6.16/2.20  tff(c_1840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1707, c_818])).
% 6.16/2.20  tff(c_1841, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1692])).
% 6.16/2.20  tff(c_40, plain, (![B_27, C_28]: (r1_tarski(k1_tarski(B_27), k2_tarski(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.16/2.20  tff(c_202, plain, (![B_27, C_28]: (k4_xboole_0(k1_tarski(B_27), k2_tarski(B_27, C_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_184])).
% 6.16/2.20  tff(c_1852, plain, (![C_28]: (k4_xboole_0('#skF_1', k2_tarski('#skF_3', C_28))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1841, c_202])).
% 6.16/2.20  tff(c_1988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1852, c_818])).
% 6.16/2.20  tff(c_1989, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_6', '#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_817])).
% 6.16/2.20  tff(c_1994, plain, (![C_18]: (r1_tarski('#skF_4', k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), C_18)) | ~r1_tarski(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_1989, c_26])).
% 6.16/2.20  tff(c_2495, plain, (![C_156]: (r1_tarski('#skF_4', k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), C_156)))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_1994])).
% 6.16/2.20  tff(c_2519, plain, (r1_tarski('#skF_4', k2_tarski('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2495])).
% 6.16/2.20  tff(c_2554, plain, (![B_157, C_158, A_159]: (k2_tarski(B_157, C_158)=A_159 | k1_tarski(C_158)=A_159 | k1_tarski(B_157)=A_159 | k1_xboole_0=A_159 | ~r1_tarski(A_159, k2_tarski(B_157, C_158)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.16/2.20  tff(c_2557, plain, (k2_tarski('#skF_6', '#skF_5')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2519, c_2554])).
% 6.16/2.20  tff(c_2588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_300, c_486, c_604, c_2557])).
% 6.16/2.20  tff(c_2589, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_603])).
% 6.16/2.20  tff(c_2746, plain, (k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_543, c_2589])).
% 6.16/2.20  tff(c_2590, plain, (k2_tarski('#skF_6', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_603])).
% 6.16/2.20  tff(c_46, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.20  tff(c_3138, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2590, c_377, c_377, c_46])).
% 6.16/2.20  tff(c_3139, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2746, c_3138])).
% 6.16/2.20  tff(c_3140, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_3139])).
% 6.16/2.20  tff(c_3153, plain, (![B_27]: (k4_xboole_0('#skF_1', k2_tarski(B_27, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3140, c_201])).
% 6.16/2.20  tff(c_3284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3153, c_2589])).
% 6.16/2.20  tff(c_3285, plain, (k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_3139])).
% 6.16/2.20  tff(c_3428, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_3285])).
% 6.16/2.20  tff(c_3429, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3428, c_2589])).
% 6.16/2.20  tff(c_3432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_3429])).
% 6.16/2.20  tff(c_3433, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_3285])).
% 6.16/2.20  tff(c_3444, plain, (![C_28]: (k4_xboole_0('#skF_1', k2_tarski('#skF_3', C_28))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3433, c_202])).
% 6.16/2.20  tff(c_3630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3444, c_2589])).
% 6.16/2.20  tff(c_3631, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_485])).
% 6.16/2.20  tff(c_3880, plain, (k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3831, c_3631])).
% 6.16/2.20  tff(c_3632, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_485])).
% 6.16/2.20  tff(c_54, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.20  tff(c_4247, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3632, c_377, c_54])).
% 6.16/2.20  tff(c_4248, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_3880, c_4247])).
% 6.16/2.20  tff(c_4249, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_4248])).
% 6.16/2.20  tff(c_4262, plain, (![B_27]: (k4_xboole_0('#skF_1', k2_tarski(B_27, '#skF_2'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4249, c_201])).
% 6.16/2.20  tff(c_4369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4262, c_3631])).
% 6.16/2.20  tff(c_4370, plain, (k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_4248])).
% 6.16/2.20  tff(c_4375, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_4370])).
% 6.16/2.20  tff(c_4376, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4375, c_3631])).
% 6.16/2.20  tff(c_4379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_4376])).
% 6.16/2.20  tff(c_4380, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_4370])).
% 6.16/2.20  tff(c_4393, plain, (![C_28]: (k4_xboole_0('#skF_1', k2_tarski('#skF_3', C_28))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4380, c_202])).
% 6.16/2.20  tff(c_4527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4393, c_3631])).
% 6.16/2.20  tff(c_4528, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 6.16/2.20  tff(c_4862, plain, (k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4799, c_4528])).
% 6.16/2.20  tff(c_4529, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_48])).
% 6.16/2.20  tff(c_50, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.20  tff(c_5615, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4529, c_50])).
% 6.16/2.20  tff(c_5616, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_4862, c_5615])).
% 6.16/2.20  tff(c_5617, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_5616])).
% 6.16/2.20  tff(c_5674, plain, (![C_295]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_295)))), inference(superposition, [status(thm), theory('equality')], [c_5617, c_40])).
% 6.16/2.20  tff(c_5692, plain, (![C_295]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_295))=k1_xboole_0)), inference(resolution, [status(thm)], [c_5674, c_22])).
% 6.16/2.20  tff(c_5699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5692, c_4528])).
% 6.16/2.20  tff(c_5700, plain, (k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_5616])).
% 6.16/2.20  tff(c_5702, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_5700])).
% 6.16/2.20  tff(c_5703, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5702, c_4528])).
% 6.16/2.20  tff(c_5706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_5703])).
% 6.16/2.20  tff(c_5707, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_5700])).
% 6.16/2.20  tff(c_5741, plain, (![B_296]: (r1_tarski('#skF_1', k2_tarski(B_296, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5707, c_38])).
% 6.16/2.20  tff(c_5763, plain, (![B_296]: (k4_xboole_0('#skF_1', k2_tarski(B_296, '#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_5741, c_22])).
% 6.16/2.20  tff(c_5857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5763, c_4528])).
% 6.16/2.20  tff(c_5859, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_56])).
% 6.16/2.20  tff(c_5860, plain, (![A_3]: (k4_xboole_0(A_3, A_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5859, c_134])).
% 6.16/2.20  tff(c_5862, plain, (![A_15]: (k4_xboole_0(A_15, '#skF_4')=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_5859, c_24])).
% 6.16/2.20  tff(c_5944, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | k4_xboole_0(A_13, B_14)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5859, c_20])).
% 6.16/2.20  tff(c_5863, plain, (![A_12]: (r1_tarski('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_5859, c_18])).
% 6.16/2.20  tff(c_6254, plain, (![A_325, C_326, B_327]: (r1_tarski(A_325, C_326) | ~r1_tarski(B_327, C_326) | ~r1_tarski(A_325, B_327))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.16/2.20  tff(c_6270, plain, (![A_328, A_329]: (r1_tarski(A_328, A_329) | ~r1_tarski(A_328, '#skF_4'))), inference(resolution, [status(thm)], [c_5863, c_6254])).
% 6.16/2.20  tff(c_6273, plain, (![A_13, A_329]: (r1_tarski(A_13, A_329) | k4_xboole_0(A_13, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_5944, c_6270])).
% 6.16/2.20  tff(c_6288, plain, (![A_330, A_331]: (r1_tarski(A_330, A_331) | A_330!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5862, c_6273])).
% 6.16/2.20  tff(c_5947, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)='#skF_4' | ~r1_tarski(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_5859, c_22])).
% 6.16/2.20  tff(c_6310, plain, (![A_332, A_333]: (k4_xboole_0(A_332, A_333)='#skF_4' | A_332!='#skF_4')), inference(resolution, [status(thm)], [c_6288, c_5947])).
% 6.16/2.20  tff(c_6034, plain, (![A_315, B_316]: (k2_xboole_0(k1_tarski(A_315), k1_tarski(B_316))=k2_tarski(A_315, B_316))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.16/2.20  tff(c_6135, plain, (![B_321, A_322]: (k2_xboole_0(k1_tarski(B_321), k1_tarski(A_322))=k2_tarski(A_322, B_321))), inference(superposition, [status(thm), theory('equality')], [c_6034, c_2])).
% 6.16/2.20  tff(c_6141, plain, (![B_321, A_322]: (k2_tarski(B_321, A_322)=k2_tarski(A_322, B_321))), inference(superposition, [status(thm), theory('equality')], [c_6135, c_32])).
% 6.16/2.20  tff(c_5858, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 6.16/2.20  tff(c_5914, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_2', '#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5859, c_5858])).
% 6.16/2.20  tff(c_6184, plain, (k4_xboole_0('#skF_1', k2_tarski('#skF_3', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6141, c_5914])).
% 6.16/2.20  tff(c_6359, plain, ('#skF_1'!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6310, c_6184])).
% 6.16/2.20  tff(c_58, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.20  tff(c_6555, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5859, c_5859, c_6141, c_58])).
% 6.16/2.20  tff(c_6556, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_6359, c_6555])).
% 6.16/2.20  tff(c_6557, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_6556])).
% 6.16/2.20  tff(c_5948, plain, (![A_308, B_309]: (k4_xboole_0(A_308, B_309)='#skF_4' | ~r1_tarski(A_308, B_309))), inference(demodulation, [status(thm), theory('equality')], [c_5859, c_22])).
% 6.16/2.20  tff(c_5966, plain, (![C_28, B_27]: (k4_xboole_0(k1_tarski(C_28), k2_tarski(B_27, C_28))='#skF_4')), inference(resolution, [status(thm)], [c_38, c_5948])).
% 6.16/2.20  tff(c_6576, plain, (![B_27]: (k4_xboole_0('#skF_1', k2_tarski(B_27, '#skF_2'))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6557, c_5966])).
% 6.16/2.20  tff(c_6751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6576, c_6184])).
% 6.16/2.20  tff(c_6752, plain, (k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_6556])).
% 6.16/2.20  tff(c_6807, plain, (k2_tarski('#skF_3', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_6752])).
% 6.16/2.20  tff(c_6808, plain, (k4_xboole_0('#skF_1', '#skF_1')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6807, c_6184])).
% 6.16/2.20  tff(c_6811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5860, c_6808])).
% 6.16/2.20  tff(c_6812, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_6752])).
% 6.16/2.20  tff(c_5967, plain, (![B_27, C_28]: (k4_xboole_0(k1_tarski(B_27), k2_tarski(B_27, C_28))='#skF_4')), inference(resolution, [status(thm)], [c_40, c_5948])).
% 6.16/2.20  tff(c_6829, plain, (![C_28]: (k4_xboole_0('#skF_1', k2_tarski('#skF_3', C_28))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6812, c_5967])).
% 6.16/2.20  tff(c_6982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6829, c_6184])).
% 6.16/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.20  
% 6.16/2.20  Inference rules
% 6.16/2.20  ----------------------
% 6.16/2.20  #Ref     : 4
% 6.16/2.20  #Sup     : 1714
% 6.16/2.21  #Fact    : 0
% 6.16/2.21  #Define  : 0
% 6.16/2.21  #Split   : 21
% 6.16/2.21  #Chain   : 0
% 6.16/2.21  #Close   : 0
% 6.16/2.21  
% 6.16/2.21  Ordering : KBO
% 6.16/2.21  
% 6.16/2.21  Simplification rules
% 6.16/2.21  ----------------------
% 6.16/2.21  #Subsume      : 94
% 6.16/2.21  #Demod        : 762
% 6.16/2.21  #Tautology    : 748
% 6.16/2.21  #SimpNegUnit  : 46
% 6.16/2.21  #BackRed      : 26
% 6.16/2.21  
% 6.16/2.21  #Partial instantiations: 0
% 6.16/2.21  #Strategies tried      : 1
% 6.16/2.21  
% 6.16/2.21  Timing (in seconds)
% 6.16/2.21  ----------------------
% 6.16/2.21  Preprocessing        : 0.30
% 6.16/2.21  Parsing              : 0.15
% 6.16/2.21  CNF conversion       : 0.02
% 6.16/2.21  Main loop            : 1.08
% 6.16/2.21  Inferencing          : 0.31
% 6.16/2.21  Reduction            : 0.44
% 6.16/2.21  Demodulation         : 0.34
% 6.16/2.21  BG Simplification    : 0.04
% 6.16/2.21  Subsumption          : 0.20
% 6.16/2.21  Abstraction          : 0.05
% 6.16/2.21  MUC search           : 0.00
% 6.16/2.21  Cooper               : 0.00
% 6.16/2.21  Total                : 1.43
% 6.16/2.21  Index Insertion      : 0.00
% 6.16/2.21  Index Deletion       : 0.00
% 6.16/2.21  Index Matching       : 0.00
% 6.16/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
