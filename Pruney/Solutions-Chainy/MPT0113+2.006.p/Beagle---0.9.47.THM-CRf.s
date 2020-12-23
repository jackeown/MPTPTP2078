%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:12 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 237 expanded)
%              Number of leaves         :   26 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 285 expanded)
%              Number of equality atoms :   52 ( 167 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_56,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_33] : k2_xboole_0(k1_xboole_0,A_33) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_10])).

tff(c_2342,plain,(
    ! [A_157,B_158] : k2_xboole_0(A_157,k4_xboole_0(B_158,A_157)) = k2_xboole_0(A_157,B_158) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2358,plain,(
    ! [B_158] : k4_xboole_0(B_158,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_2342,c_72])).

tff(c_2382,plain,(
    ! [B_159] : k4_xboole_0(B_159,k1_xboole_0) = B_159 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2358])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2412,plain,(
    ! [B_159] : r1_tarski(B_159,B_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_2382,c_14])).

tff(c_30,plain,(
    ! [A_23,C_25,B_24] :
      ( r1_xboole_0(A_23,k4_xboole_0(C_25,B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1892,plain,(
    ! [A_124,B_125] : r1_xboole_0(k4_xboole_0(A_124,B_125),k4_xboole_0(B_125,A_124)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_17] :
      ( ~ r1_xboole_0(A_17,A_17)
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1901,plain,(
    ! [B_125] : k4_xboole_0(B_125,B_125) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1892,c_20])).

tff(c_2433,plain,(
    ! [B_160] : r1_tarski(B_160,B_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_2382,c_14])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2572,plain,(
    ! [B_167] : k3_xboole_0(B_167,B_167) = B_167 ),
    inference(resolution,[status(thm)],[c_2433,c_12])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2578,plain,(
    ! [B_167] : k5_xboole_0(B_167,B_167) = k4_xboole_0(B_167,B_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_2572,c_6])).

tff(c_2591,plain,(
    ! [B_167] : k5_xboole_0(B_167,B_167) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1901,c_2578])).

tff(c_32,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_141,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_144,plain,(
    ! [A_35,B_36] : r1_xboole_0(k4_xboole_0(A_35,B_36),k4_xboole_0(B_36,A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_153,plain,(
    ! [B_36] : k4_xboole_0(B_36,B_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_144,c_20])).

tff(c_367,plain,(
    ! [A_60,B_61] : k2_xboole_0(A_60,k4_xboole_0(B_61,A_60)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_383,plain,(
    ! [B_61] : k4_xboole_0(B_61,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_72])).

tff(c_407,plain,(
    ! [B_62] : k4_xboole_0(B_62,k1_xboole_0) = B_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_383])).

tff(c_458,plain,(
    ! [B_64] : r1_tarski(B_64,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_14])).

tff(c_537,plain,(
    ! [B_67] : k3_xboole_0(B_67,B_67) = B_67 ),
    inference(resolution,[status(thm)],[c_458,c_12])).

tff(c_543,plain,(
    ! [B_67] : k5_xboole_0(B_67,B_67) = k4_xboole_0(B_67,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_6])).

tff(c_556,plain,(
    ! [B_67] : k5_xboole_0(B_67,B_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_543])).

tff(c_172,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_937,plain,(
    ! [A_89,B_90] : k3_xboole_0(k4_xboole_0(A_89,B_90),A_89) = k4_xboole_0(A_89,B_90) ),
    inference(resolution,[status(thm)],[c_14,c_172])).

tff(c_943,plain,(
    ! [A_89,B_90] : k5_xboole_0(k4_xboole_0(A_89,B_90),k4_xboole_0(A_89,B_90)) = k4_xboole_0(k4_xboole_0(A_89,B_90),A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_6])).

tff(c_970,plain,(
    ! [A_91,B_92] : k4_xboole_0(k4_xboole_0(A_91,B_92),A_91) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_943])).

tff(c_16,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_988,plain,(
    ! [A_91,B_92] : k2_xboole_0(A_91,k4_xboole_0(A_91,B_92)) = k2_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_16])).

tff(c_1027,plain,(
    ! [A_91,B_92] : k2_xboole_0(A_91,k4_xboole_0(A_91,B_92)) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_988])).

tff(c_34,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_180,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_172])).

tff(c_268,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_277,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_268])).

tff(c_389,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k5_xboole_0('#skF_1','#skF_1')) = k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_367])).

tff(c_403,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k5_xboole_0('#skF_1','#skF_1')) = k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_389])).

tff(c_1757,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_556,c_403])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_668,plain,(
    ! [A_73,B_74] : r1_tarski(A_73,k2_xboole_0(A_73,B_74)) ),
    inference(resolution,[status(thm)],[c_458,c_8])).

tff(c_700,plain,(
    ! [A_75,B_76] : r1_tarski(A_75,k2_xboole_0(B_76,A_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_668])).

tff(c_726,plain,(
    ! [A_7,B_76,B_8] : r1_tarski(A_7,k2_xboole_0(B_76,k2_xboole_0(A_7,B_8))) ),
    inference(resolution,[status(thm)],[c_700,c_8])).

tff(c_1855,plain,(
    ! [B_123] : r1_tarski('#skF_1',k2_xboole_0(B_123,k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1757,c_726])).

tff(c_1864,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_1855])).

tff(c_1888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_1864])).

tff(c_1890,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1922,plain,(
    ! [A_128,B_129] :
      ( k3_xboole_0(A_128,B_129) = A_128
      | ~ r1_tarski(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1936,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1890,c_1922])).

tff(c_1981,plain,(
    ! [A_137,B_138] : k5_xboole_0(A_137,k3_xboole_0(A_137,B_138)) = k4_xboole_0(A_137,B_138) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1996,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1936,c_1981])).

tff(c_2601,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2591,c_1996])).

tff(c_1938,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_1922])).

tff(c_1990,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1938,c_1981])).

tff(c_2070,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1996,c_1990])).

tff(c_2364,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1','#skF_2')) = k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2070,c_2342])).

tff(c_2378,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2','#skF_3'),k4_xboole_0('#skF_1','#skF_2')) = k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2364])).

tff(c_4342,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2,c_2601,c_2378])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_xboole_0(A_18,B_19)
      | ~ r1_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4902,plain,(
    ! [A_247] :
      ( r1_xboole_0(A_247,'#skF_1')
      | ~ r1_xboole_0(A_247,k4_xboole_0('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4342,c_26])).

tff(c_4951,plain,(
    ! [A_248] :
      ( r1_xboole_0(A_248,'#skF_1')
      | ~ r1_tarski(A_248,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_4902])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5009,plain,(
    ! [A_252] :
      ( r1_xboole_0('#skF_1',A_252)
      | ~ r1_tarski(A_252,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4951,c_4])).

tff(c_1889,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_5028,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_5009,c_1889])).

tff(c_5042,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_5028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.89  
% 4.37/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.89  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.37/1.89  
% 4.37/1.89  %Foreground sorts:
% 4.37/1.89  
% 4.37/1.89  
% 4.37/1.89  %Background operators:
% 4.37/1.89  
% 4.37/1.89  
% 4.37/1.89  %Foreground operators:
% 4.37/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.37/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.37/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.37/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.37/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.37/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.37/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.37/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.37/1.89  
% 4.37/1.90  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.37/1.90  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.37/1.90  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.37/1.90  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.37/1.90  tff(f_81, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 4.37/1.90  tff(f_77, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 4.37/1.90  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 4.37/1.90  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.37/1.90  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.37/1.90  tff(f_88, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.37/1.90  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.37/1.90  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.37/1.90  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.37/1.90  tff(c_56, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.37/1.90  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.37/1.90  tff(c_72, plain, (![A_33]: (k2_xboole_0(k1_xboole_0, A_33)=A_33)), inference(superposition, [status(thm), theory('equality')], [c_56, c_10])).
% 4.37/1.90  tff(c_2342, plain, (![A_157, B_158]: (k2_xboole_0(A_157, k4_xboole_0(B_158, A_157))=k2_xboole_0(A_157, B_158))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.37/1.90  tff(c_2358, plain, (![B_158]: (k4_xboole_0(B_158, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_158))), inference(superposition, [status(thm), theory('equality')], [c_2342, c_72])).
% 4.37/1.90  tff(c_2382, plain, (![B_159]: (k4_xboole_0(B_159, k1_xboole_0)=B_159)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2358])).
% 4.37/1.90  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.37/1.90  tff(c_2412, plain, (![B_159]: (r1_tarski(B_159, B_159))), inference(superposition, [status(thm), theory('equality')], [c_2382, c_14])).
% 4.37/1.90  tff(c_30, plain, (![A_23, C_25, B_24]: (r1_xboole_0(A_23, k4_xboole_0(C_25, B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.37/1.90  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.37/1.90  tff(c_1892, plain, (![A_124, B_125]: (r1_xboole_0(k4_xboole_0(A_124, B_125), k4_xboole_0(B_125, A_124)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.37/1.90  tff(c_20, plain, (![A_17]: (~r1_xboole_0(A_17, A_17) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.37/1.90  tff(c_1901, plain, (![B_125]: (k4_xboole_0(B_125, B_125)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1892, c_20])).
% 4.37/1.90  tff(c_2433, plain, (![B_160]: (r1_tarski(B_160, B_160))), inference(superposition, [status(thm), theory('equality')], [c_2382, c_14])).
% 4.37/1.90  tff(c_12, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.37/1.90  tff(c_2572, plain, (![B_167]: (k3_xboole_0(B_167, B_167)=B_167)), inference(resolution, [status(thm)], [c_2433, c_12])).
% 4.37/1.90  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/1.90  tff(c_2578, plain, (![B_167]: (k5_xboole_0(B_167, B_167)=k4_xboole_0(B_167, B_167))), inference(superposition, [status(thm), theory('equality')], [c_2572, c_6])).
% 4.37/1.90  tff(c_2591, plain, (![B_167]: (k5_xboole_0(B_167, B_167)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1901, c_2578])).
% 4.37/1.90  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.37/1.90  tff(c_141, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_32])).
% 4.37/1.90  tff(c_144, plain, (![A_35, B_36]: (r1_xboole_0(k4_xboole_0(A_35, B_36), k4_xboole_0(B_36, A_35)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.37/1.90  tff(c_153, plain, (![B_36]: (k4_xboole_0(B_36, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_20])).
% 4.37/1.90  tff(c_367, plain, (![A_60, B_61]: (k2_xboole_0(A_60, k4_xboole_0(B_61, A_60))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.37/1.90  tff(c_383, plain, (![B_61]: (k4_xboole_0(B_61, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_61))), inference(superposition, [status(thm), theory('equality')], [c_367, c_72])).
% 4.37/1.90  tff(c_407, plain, (![B_62]: (k4_xboole_0(B_62, k1_xboole_0)=B_62)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_383])).
% 4.37/1.90  tff(c_458, plain, (![B_64]: (r1_tarski(B_64, B_64))), inference(superposition, [status(thm), theory('equality')], [c_407, c_14])).
% 4.37/1.90  tff(c_537, plain, (![B_67]: (k3_xboole_0(B_67, B_67)=B_67)), inference(resolution, [status(thm)], [c_458, c_12])).
% 4.37/1.90  tff(c_543, plain, (![B_67]: (k5_xboole_0(B_67, B_67)=k4_xboole_0(B_67, B_67))), inference(superposition, [status(thm), theory('equality')], [c_537, c_6])).
% 4.37/1.90  tff(c_556, plain, (![B_67]: (k5_xboole_0(B_67, B_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_543])).
% 4.37/1.90  tff(c_172, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=A_38 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.37/1.90  tff(c_937, plain, (![A_89, B_90]: (k3_xboole_0(k4_xboole_0(A_89, B_90), A_89)=k4_xboole_0(A_89, B_90))), inference(resolution, [status(thm)], [c_14, c_172])).
% 4.37/1.90  tff(c_943, plain, (![A_89, B_90]: (k5_xboole_0(k4_xboole_0(A_89, B_90), k4_xboole_0(A_89, B_90))=k4_xboole_0(k4_xboole_0(A_89, B_90), A_89))), inference(superposition, [status(thm), theory('equality')], [c_937, c_6])).
% 4.37/1.90  tff(c_970, plain, (![A_91, B_92]: (k4_xboole_0(k4_xboole_0(A_91, B_92), A_91)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_556, c_943])).
% 4.37/1.90  tff(c_16, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.37/1.90  tff(c_988, plain, (![A_91, B_92]: (k2_xboole_0(A_91, k4_xboole_0(A_91, B_92))=k2_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_970, c_16])).
% 4.37/1.90  tff(c_1027, plain, (![A_91, B_92]: (k2_xboole_0(A_91, k4_xboole_0(A_91, B_92))=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_988])).
% 4.37/1.90  tff(c_34, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.37/1.90  tff(c_180, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_34, c_172])).
% 4.37/1.90  tff(c_268, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/1.90  tff(c_277, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_180, c_268])).
% 4.37/1.90  tff(c_389, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k5_xboole_0('#skF_1', '#skF_1'))=k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_277, c_367])).
% 4.37/1.90  tff(c_403, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k5_xboole_0('#skF_1', '#skF_1'))=k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_389])).
% 4.37/1.90  tff(c_1757, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_556, c_403])).
% 4.37/1.90  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.37/1.90  tff(c_668, plain, (![A_73, B_74]: (r1_tarski(A_73, k2_xboole_0(A_73, B_74)))), inference(resolution, [status(thm)], [c_458, c_8])).
% 4.37/1.90  tff(c_700, plain, (![A_75, B_76]: (r1_tarski(A_75, k2_xboole_0(B_76, A_75)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_668])).
% 4.37/1.90  tff(c_726, plain, (![A_7, B_76, B_8]: (r1_tarski(A_7, k2_xboole_0(B_76, k2_xboole_0(A_7, B_8))))), inference(resolution, [status(thm)], [c_700, c_8])).
% 4.37/1.90  tff(c_1855, plain, (![B_123]: (r1_tarski('#skF_1', k2_xboole_0(B_123, k4_xboole_0('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1757, c_726])).
% 4.37/1.90  tff(c_1864, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1027, c_1855])).
% 4.37/1.90  tff(c_1888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_1864])).
% 4.37/1.90  tff(c_1890, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_32])).
% 4.37/1.90  tff(c_1922, plain, (![A_128, B_129]: (k3_xboole_0(A_128, B_129)=A_128 | ~r1_tarski(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.37/1.90  tff(c_1936, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_1890, c_1922])).
% 4.37/1.90  tff(c_1981, plain, (![A_137, B_138]: (k5_xboole_0(A_137, k3_xboole_0(A_137, B_138))=k4_xboole_0(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/1.90  tff(c_1996, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1936, c_1981])).
% 4.37/1.90  tff(c_2601, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2591, c_1996])).
% 4.37/1.90  tff(c_1938, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_34, c_1922])).
% 4.37/1.90  tff(c_1990, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1938, c_1981])).
% 4.37/1.90  tff(c_2070, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1996, c_1990])).
% 4.37/1.90  tff(c_2364, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', '#skF_2'))=k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2070, c_2342])).
% 4.37/1.90  tff(c_2378, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), k4_xboole_0('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2364])).
% 4.37/1.90  tff(c_4342, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2, c_2601, c_2378])).
% 4.37/1.90  tff(c_26, plain, (![A_18, B_19, C_20]: (r1_xboole_0(A_18, B_19) | ~r1_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.37/1.90  tff(c_4902, plain, (![A_247]: (r1_xboole_0(A_247, '#skF_1') | ~r1_xboole_0(A_247, k4_xboole_0('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4342, c_26])).
% 4.37/1.90  tff(c_4951, plain, (![A_248]: (r1_xboole_0(A_248, '#skF_1') | ~r1_tarski(A_248, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_4902])).
% 4.37/1.90  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.90  tff(c_5009, plain, (![A_252]: (r1_xboole_0('#skF_1', A_252) | ~r1_tarski(A_252, '#skF_3'))), inference(resolution, [status(thm)], [c_4951, c_4])).
% 4.37/1.90  tff(c_1889, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 4.37/1.90  tff(c_5028, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_5009, c_1889])).
% 4.37/1.90  tff(c_5042, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2412, c_5028])).
% 4.37/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.90  
% 4.37/1.90  Inference rules
% 4.37/1.90  ----------------------
% 4.37/1.90  #Ref     : 0
% 4.37/1.90  #Sup     : 1217
% 4.37/1.90  #Fact    : 0
% 4.37/1.90  #Define  : 0
% 4.37/1.90  #Split   : 3
% 4.37/1.90  #Chain   : 0
% 4.37/1.90  #Close   : 0
% 4.37/1.90  
% 4.37/1.90  Ordering : KBO
% 4.37/1.90  
% 4.37/1.90  Simplification rules
% 4.37/1.90  ----------------------
% 4.37/1.90  #Subsume      : 58
% 4.37/1.90  #Demod        : 881
% 4.37/1.90  #Tautology    : 926
% 4.37/1.90  #SimpNegUnit  : 1
% 4.37/1.90  #BackRed      : 17
% 4.37/1.90  
% 4.37/1.90  #Partial instantiations: 0
% 4.37/1.90  #Strategies tried      : 1
% 4.37/1.90  
% 4.37/1.90  Timing (in seconds)
% 4.37/1.91  ----------------------
% 4.37/1.91  Preprocessing        : 0.30
% 4.37/1.91  Parsing              : 0.17
% 4.37/1.91  CNF conversion       : 0.02
% 4.37/1.91  Main loop            : 0.81
% 4.37/1.91  Inferencing          : 0.26
% 4.37/1.91  Reduction            : 0.32
% 4.37/1.91  Demodulation         : 0.25
% 4.37/1.91  BG Simplification    : 0.03
% 4.37/1.91  Subsumption          : 0.14
% 4.37/1.91  Abstraction          : 0.03
% 4.37/1.91  MUC search           : 0.00
% 4.37/1.91  Cooper               : 0.00
% 4.37/1.91  Total                : 1.14
% 4.37/1.91  Index Insertion      : 0.00
% 4.37/1.91  Index Deletion       : 0.00
% 4.37/1.91  Index Matching       : 0.00
% 4.37/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
