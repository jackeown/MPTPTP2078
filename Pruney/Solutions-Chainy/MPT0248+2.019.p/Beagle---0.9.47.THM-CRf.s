%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:06 EST 2020

% Result     : Theorem 8.02s
% Output     : CNFRefutation 8.26s
% Verified   : 
% Statistics : Number of formulae       :  249 (2242 expanded)
%              Number of leaves         :   47 ( 773 expanded)
%              Depth                    :   19
%              Number of atoms          :  299 (3406 expanded)
%              Number of equality atoms :  187 (2974 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_89,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_83,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_98,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_141,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_92,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k1_tarski(A_75),B_76)
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_96,plain,
    ( k1_xboole_0 != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_146,plain,(
    k1_tarski('#skF_7') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_102,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_147,plain,(
    ! [A_86,B_87] : r1_tarski(A_86,k2_xboole_0(A_86,B_87)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_150,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_147])).

tff(c_507,plain,(
    ! [B_127,A_128] :
      ( B_127 = A_128
      | ~ r1_tarski(B_127,A_128)
      | ~ r1_tarski(A_128,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_515,plain,
    ( k1_tarski('#skF_7') = '#skF_8'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_150,c_507])).

tff(c_525,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_515])).

tff(c_534,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_92,c_525])).

tff(c_40,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_4'(A_22),A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_60,plain,(
    ! [A_39] : k5_xboole_0(A_39,A_39) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    ! [A_20] : k3_xboole_0(A_20,A_20) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ! [A_18] : k2_xboole_0(A_18,A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7348,plain,(
    ! [A_350,B_351] : k5_xboole_0(k5_xboole_0(A_350,B_351),k2_xboole_0(A_350,B_351)) = k3_xboole_0(A_350,B_351) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7448,plain,(
    ! [A_18] : k5_xboole_0(k5_xboole_0(A_18,A_18),A_18) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_7348])).

tff(c_7465,plain,(
    ! [A_352] : k5_xboole_0(k1_xboole_0,A_352) = A_352 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_38,c_7448])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7503,plain,(
    ! [A_352] : k5_xboole_0(A_352,k1_xboole_0) = A_352 ),
    inference(superposition,[status(thm),theory(equality)],[c_7465,c_4])).

tff(c_48,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1395,plain,(
    ! [A_159,B_160,C_161] : k5_xboole_0(k5_xboole_0(A_159,B_160),C_161) = k5_xboole_0(A_159,k5_xboole_0(B_160,C_161)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1176,plain,(
    ! [A_154,B_155] : k5_xboole_0(k5_xboole_0(A_154,B_155),k2_xboole_0(A_154,B_155)) = k3_xboole_0(A_154,B_155) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1242,plain,(
    k5_xboole_0(k5_xboole_0('#skF_8','#skF_9'),k1_tarski('#skF_7')) = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1176])).

tff(c_1404,plain,(
    k5_xboole_0('#skF_8',k5_xboole_0('#skF_9',k1_tarski('#skF_7'))) = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1395,c_1242])).

tff(c_1245,plain,(
    ! [A_18] : k5_xboole_0(k5_xboole_0(A_18,A_18),A_18) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1176])).

tff(c_1255,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_60,c_1245])).

tff(c_1481,plain,(
    ! [A_39,C_161] : k5_xboole_0(A_39,k5_xboole_0(A_39,C_161)) = k5_xboole_0(k1_xboole_0,C_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1395])).

tff(c_1494,plain,(
    ! [A_39,C_161] : k5_xboole_0(A_39,k5_xboole_0(A_39,C_161)) = C_161 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_1481])).

tff(c_1664,plain,(
    k5_xboole_0('#skF_9',k1_tarski('#skF_7')) = k5_xboole_0('#skF_8',k3_xboole_0('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_1494])).

tff(c_1673,plain,(
    k5_xboole_0('#skF_9',k1_tarski('#skF_7')) = k4_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1664])).

tff(c_1495,plain,(
    ! [A_162,C_163] : k5_xboole_0(A_162,k5_xboole_0(A_162,C_163)) = C_163 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_1481])).

tff(c_1550,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1495])).

tff(c_1928,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k4_xboole_0('#skF_8','#skF_9')) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1673,c_1550])).

tff(c_155,plain,(
    ! [B_88,A_89] : k2_xboole_0(B_88,A_89) = k2_xboole_0(A_89,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_34,B_35] : r1_tarski(A_34,k2_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_195,plain,(
    ! [A_91,B_92] : r1_tarski(A_91,k2_xboole_0(B_92,A_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_56])).

tff(c_204,plain,(
    r1_tarski('#skF_9',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_195])).

tff(c_343,plain,(
    ! [A_114,B_115] :
      ( k2_xboole_0(A_114,B_115) = B_115
      | ~ r1_tarski(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_363,plain,(
    k2_xboole_0('#skF_9',k1_tarski('#skF_7')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_204,c_343])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1569,plain,(
    ! [A_164,B_165] : k5_xboole_0(A_164,k5_xboole_0(B_165,A_164)) = B_165 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1495])).

tff(c_1605,plain,(
    ! [A_39,C_161] : k5_xboole_0(k5_xboole_0(A_39,C_161),C_161) = A_39 ),
    inference(superposition,[status(thm),theory(equality)],[c_1494,c_1569])).

tff(c_1922,plain,(
    k5_xboole_0(k4_xboole_0('#skF_8','#skF_9'),k1_tarski('#skF_7')) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1673,c_1605])).

tff(c_1975,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),'#skF_9') = k4_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1922,c_1550])).

tff(c_62,plain,(
    ! [A_40,B_41] : k5_xboole_0(k5_xboole_0(A_40,B_41),k2_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2110,plain,(
    k5_xboole_0(k4_xboole_0('#skF_8','#skF_9'),k2_xboole_0(k1_tarski('#skF_7'),'#skF_9')) = k3_xboole_0(k1_tarski('#skF_7'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1975,c_62])).

tff(c_2129,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_4,c_363,c_2,c_2110])).

tff(c_16,plain,(
    ! [D_15,A_10,B_11] :
      ( r2_hidden(D_15,A_10)
      | ~ r2_hidden(D_15,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2194,plain,(
    ! [D_179] :
      ( r2_hidden(D_179,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_179,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2129,c_16])).

tff(c_64,plain,(
    ! [C_46,A_42] :
      ( C_46 = A_42
      | ~ r2_hidden(C_46,k1_tarski(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2207,plain,(
    ! [D_180] :
      ( D_180 = '#skF_7'
      | ~ r2_hidden(D_180,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2194,c_64])).

tff(c_2217,plain,
    ( '#skF_4'('#skF_9') = '#skF_7'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_40,c_2207])).

tff(c_2218,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_2217])).

tff(c_2226,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_141])).

tff(c_2225,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_4'(A_22),A_22)
      | A_22 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_40])).

tff(c_365,plain,(
    k2_xboole_0('#skF_8',k1_tarski('#skF_7')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_150,c_343])).

tff(c_435,plain,(
    ! [A_122,B_123] : k2_xboole_0(A_122,k2_xboole_0(A_122,B_123)) = k2_xboole_0(A_122,B_123) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_469,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_435])).

tff(c_170,plain,(
    ! [A_89,B_88] : r1_tarski(A_89,k2_xboole_0(B_88,A_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_56])).

tff(c_827,plain,(
    ! [A_145,B_146] : k2_xboole_0(A_145,k2_xboole_0(B_146,A_145)) = k2_xboole_0(B_146,A_145) ),
    inference(resolution,[status(thm)],[c_170,c_343])).

tff(c_901,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_827])).

tff(c_1045,plain,(
    ! [B_152,A_153] : k2_xboole_0(B_152,k2_xboole_0(B_152,A_153)) = k2_xboole_0(A_153,B_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_827])).

tff(c_1094,plain,(
    ! [B_2,A_1] : k2_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k2_xboole_0(B_2,k2_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_1045])).

tff(c_3770,plain,(
    ! [B_237,A_238] : k2_xboole_0(k2_xboole_0(B_237,A_238),B_237) = k2_xboole_0(B_237,A_238) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_1094])).

tff(c_3791,plain,(
    ! [B_237,A_238] : k5_xboole_0(k5_xboole_0(k2_xboole_0(B_237,A_238),B_237),k2_xboole_0(B_237,A_238)) = k3_xboole_0(k2_xboole_0(B_237,A_238),B_237) ),
    inference(superposition,[status(thm),theory(equality)],[c_3770,c_62])).

tff(c_3920,plain,(
    ! [B_239,A_240] : k3_xboole_0(k2_xboole_0(B_239,A_240),B_239) = B_239 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1550,c_4,c_4,c_3791])).

tff(c_3971,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_3920])).

tff(c_4201,plain,(
    ! [D_246] :
      ( r2_hidden(D_246,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_246,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3971,c_16])).

tff(c_4246,plain,(
    ! [D_250] :
      ( D_250 = '#skF_7'
      | ~ r2_hidden(D_250,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4201,c_64])).

tff(c_4262,plain,
    ( '#skF_4'('#skF_8') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2225,c_4246])).

tff(c_4279,plain,(
    '#skF_4'('#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_2226,c_4262])).

tff(c_4286,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | '#skF_9' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_4279,c_2225])).

tff(c_4290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2226,c_534,c_4286])).

tff(c_4292,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2217])).

tff(c_521,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_204,c_507])).

tff(c_549,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_521])).

tff(c_553,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_92,c_549])).

tff(c_4291,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2217])).

tff(c_4339,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_4291,c_40])).

tff(c_4343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4292,c_553,c_4339])).

tff(c_4344,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_521])).

tff(c_4352,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4344,c_102])).

tff(c_7421,plain,(
    k5_xboole_0(k5_xboole_0('#skF_8','#skF_9'),'#skF_9') = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_4352,c_7348])).

tff(c_58,plain,(
    ! [A_36,B_37,C_38] : k5_xboole_0(k5_xboole_0(A_36,B_37),C_38) = k5_xboole_0(A_36,k5_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7630,plain,(
    k5_xboole_0('#skF_8',k5_xboole_0('#skF_9','#skF_9')) = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_7421,c_58])).

tff(c_7649,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7503,c_60,c_7630])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8169,plain,(
    ! [D_369] :
      ( r2_hidden(D_369,'#skF_9')
      | ~ r2_hidden(D_369,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7649,c_14])).

tff(c_4376,plain,(
    ! [C_46] :
      ( C_46 = '#skF_7'
      | ~ r2_hidden(C_46,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4344,c_64])).

tff(c_8200,plain,(
    ! [D_370] :
      ( D_370 = '#skF_7'
      | ~ r2_hidden(D_370,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8169,c_4376])).

tff(c_8212,plain,
    ( '#skF_4'('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_40,c_8200])).

tff(c_8217,plain,(
    '#skF_4'('#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_8212])).

tff(c_8260,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_8217,c_40])).

tff(c_8264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_534,c_8260])).

tff(c_8265,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_8266,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_100,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_8276,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8266,c_8266,c_100])).

tff(c_8267,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8266,c_102])).

tff(c_8290,plain,(
    ! [B_376,A_377] : k2_xboole_0(B_376,A_377) = k2_xboole_0(A_377,B_376) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8329,plain,(
    ! [A_378,B_379] : r1_tarski(A_378,k2_xboole_0(B_379,A_378)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8290,c_56])).

tff(c_8338,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_8267,c_8329])).

tff(c_8756,plain,(
    ! [B_418,A_419] :
      ( B_418 = A_419
      | ~ r1_tarski(B_418,A_419)
      | ~ r1_tarski(A_419,B_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8760,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_8338,c_8756])).

tff(c_8770,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_8276,c_8760])).

tff(c_8818,plain,(
    ! [A_427,B_428] :
      ( r2_hidden('#skF_1'(A_427,B_428),A_427)
      | r1_tarski(A_427,B_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8348,plain,(
    ! [C_383,A_384] :
      ( C_383 = A_384
      | ~ r2_hidden(C_383,k1_tarski(A_384)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8355,plain,(
    ! [C_383] :
      ( C_383 = '#skF_7'
      | ~ r2_hidden(C_383,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8266,c_8348])).

tff(c_8840,plain,(
    ! [B_429] :
      ( '#skF_1'('#skF_8',B_429) = '#skF_7'
      | r1_tarski('#skF_8',B_429) ) ),
    inference(resolution,[status(thm)],[c_8818,c_8355])).

tff(c_8856,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_8840,c_8770])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8866,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_8856,c_8])).

tff(c_8871,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_8770,c_8866])).

tff(c_10313,plain,(
    ! [A_470,B_471] : k5_xboole_0(k5_xboole_0(A_470,B_471),k2_xboole_0(A_470,B_471)) = k3_xboole_0(A_470,B_471) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10382,plain,(
    ! [A_18] : k5_xboole_0(k5_xboole_0(A_18,A_18),A_18) = k3_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_10313])).

tff(c_10394,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_38,c_10382])).

tff(c_10534,plain,(
    ! [A_475,B_476,C_477] : k5_xboole_0(k5_xboole_0(A_475,B_476),C_477) = k5_xboole_0(A_475,k5_xboole_0(B_476,C_477)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10620,plain,(
    ! [A_39,C_477] : k5_xboole_0(A_39,k5_xboole_0(A_39,C_477)) = k5_xboole_0(k1_xboole_0,C_477) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_10534])).

tff(c_10636,plain,(
    ! [A_478,C_479] : k5_xboole_0(A_478,k5_xboole_0(A_478,C_479)) = C_479 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10394,c_10620])).

tff(c_10710,plain,(
    ! [A_480,B_481] : k5_xboole_0(A_480,k5_xboole_0(B_481,A_480)) = B_481 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_10636])).

tff(c_10691,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_10636])).

tff(c_10713,plain,(
    ! [B_481,A_480] : k5_xboole_0(k5_xboole_0(B_481,A_480),B_481) = A_480 ),
    inference(superposition,[status(thm),theory(equality)],[c_10710,c_10691])).

tff(c_10379,plain,(
    k5_xboole_0(k5_xboole_0('#skF_8','#skF_9'),'#skF_8') = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_8267,c_10313])).

tff(c_10893,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10713,c_10379])).

tff(c_11258,plain,(
    ! [D_494] :
      ( r2_hidden(D_494,'#skF_8')
      | ~ r2_hidden(D_494,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10893,c_16])).

tff(c_11274,plain,
    ( r2_hidden('#skF_4'('#skF_9'),'#skF_8')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_40,c_11258])).

tff(c_11282,plain,(
    r2_hidden('#skF_4'('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_8265,c_11274])).

tff(c_11289,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_11282,c_8355])).

tff(c_11295,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_11289,c_40])).

tff(c_11299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8265,c_8871,c_11295])).

tff(c_11301,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_11318,plain,
    ( '#skF_9' != '#skF_8'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11301,c_96])).

tff(c_11319,plain,(
    k1_tarski('#skF_7') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_11318])).

tff(c_11302,plain,(
    ! [A_39] : k5_xboole_0(A_39,A_39) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11301,c_60])).

tff(c_11367,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_4'(A_22),A_22)
      | A_22 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11301,c_40])).

tff(c_12548,plain,(
    ! [A_571,B_572] : k5_xboole_0(k5_xboole_0(A_571,B_572),k2_xboole_0(A_571,B_572)) = k3_xboole_0(A_571,B_572) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12645,plain,(
    ! [A_39] : k5_xboole_0('#skF_8',k2_xboole_0(A_39,A_39)) = k3_xboole_0(A_39,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_11302,c_12548])).

tff(c_12655,plain,(
    ! [A_39] : k5_xboole_0('#skF_8',A_39) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_12645])).

tff(c_12642,plain,(
    k5_xboole_0(k5_xboole_0('#skF_8','#skF_9'),k1_tarski('#skF_7')) = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_12548])).

tff(c_12813,plain,(
    k5_xboole_0('#skF_9',k1_tarski('#skF_7')) = k3_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12655,c_12642])).

tff(c_12223,plain,(
    ! [A_562,B_563,C_564] : k5_xboole_0(k5_xboole_0(A_562,B_563),C_564) = k5_xboole_0(A_562,k5_xboole_0(B_563,C_564)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12273,plain,(
    ! [A_39,C_564] : k5_xboole_0(A_39,k5_xboole_0(A_39,C_564)) = k5_xboole_0('#skF_8',C_564) ),
    inference(superposition,[status(thm),theory(equality)],[c_11302,c_12223])).

tff(c_12831,plain,(
    ! [A_575,C_576] : k5_xboole_0(A_575,k5_xboole_0(A_575,C_576)) = C_576 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12655,c_12273])).

tff(c_12959,plain,(
    ! [B_582,A_583] : k5_xboole_0(B_582,k5_xboole_0(A_583,B_582)) = A_583 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_12831])).

tff(c_13002,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_8','#skF_9')) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_12813,c_12959])).

tff(c_11374,plain,(
    ! [B_503,A_504] : k2_xboole_0(B_503,A_504) = k2_xboole_0(A_504,B_503) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_11413,plain,(
    ! [A_505,B_506] : r1_tarski(A_505,k2_xboole_0(B_506,A_505)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11374,c_56])).

tff(c_11422,plain,(
    r1_tarski('#skF_9',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_11413])).

tff(c_11477,plain,(
    ! [A_518,B_519] :
      ( k2_xboole_0(A_518,B_519) = B_519
      | ~ r1_tarski(A_518,B_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_11497,plain,(
    k2_xboole_0('#skF_9',k1_tarski('#skF_7')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_11422,c_11477])).

tff(c_12657,plain,(
    ! [A_39,C_564] : k5_xboole_0(A_39,k5_xboole_0(A_39,C_564)) = C_564 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12655,c_12273])).

tff(c_13375,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),'#skF_9') = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_13002,c_12657])).

tff(c_13405,plain,(
    k5_xboole_0(k3_xboole_0('#skF_8','#skF_9'),k2_xboole_0(k1_tarski('#skF_7'),'#skF_9')) = k3_xboole_0(k1_tarski('#skF_7'),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_13375,c_62])).

tff(c_13426,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13002,c_4,c_11497,c_2,c_13405])).

tff(c_13520,plain,(
    ! [D_595] :
      ( r2_hidden(D_595,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_595,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13426,c_16])).

tff(c_13533,plain,(
    ! [D_596] :
      ( D_596 = '#skF_7'
      | ~ r2_hidden(D_596,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_13520,c_64])).

tff(c_13548,plain,
    ( '#skF_4'('#skF_9') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_11367,c_13533])).

tff(c_13549,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_13548])).

tff(c_12907,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k5_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_12831])).

tff(c_13372,plain,(
    k5_xboole_0(k3_xboole_0('#skF_8','#skF_9'),'#skF_9') = k1_tarski('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_13002,c_12907])).

tff(c_13553,plain,(
    k5_xboole_0(k3_xboole_0('#skF_8','#skF_8'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13549,c_13549,c_13372])).

tff(c_13566,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11302,c_38,c_13553])).

tff(c_13568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11319,c_13566])).

tff(c_13570,plain,(
    '#skF_9' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_13548])).

tff(c_11300,plain,(
    k1_tarski('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_11596,plain,(
    ! [B_529,A_530] :
      ( B_529 = A_530
      | ~ r1_tarski(B_529,A_530)
      | ~ r1_tarski(A_530,B_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_11600,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_11422,c_11596])).

tff(c_11612,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_11300,c_11600])).

tff(c_11629,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_92,c_11612])).

tff(c_13569,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_13548])).

tff(c_13574,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_13569,c_11367])).

tff(c_13578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13570,c_11629,c_13574])).

tff(c_13579,plain,(
    '#skF_9' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_11318])).

tff(c_13580,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_11318])).

tff(c_13581,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13580,c_102])).

tff(c_13605,plain,(
    ! [B_599,A_600] : k2_xboole_0(B_599,A_600) = k2_xboole_0(A_600,B_599) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_13644,plain,(
    ! [A_601,B_602] : r1_tarski(A_601,k2_xboole_0(B_602,A_601)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13605,c_56])).

tff(c_13653,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_13581,c_13644])).

tff(c_14170,plain,(
    ! [B_653,A_654] :
      ( B_653 = A_654
      | ~ r1_tarski(B_653,A_654)
      | ~ r1_tarski(A_654,B_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14176,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_13653,c_14170])).

tff(c_14187,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_13579,c_14176])).

tff(c_14113,plain,(
    ! [A_649,B_650] :
      ( r2_hidden('#skF_1'(A_649,B_650),A_649)
      | r1_tarski(A_649,B_650) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_13661,plain,(
    ! [C_603,A_604] :
      ( C_603 = A_604
      | ~ r2_hidden(C_603,k1_tarski(A_604)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_13664,plain,(
    ! [C_603] :
      ( C_603 = '#skF_7'
      | ~ r2_hidden(C_603,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13580,c_13661])).

tff(c_14138,plain,(
    ! [B_650] :
      ( '#skF_1'('#skF_8',B_650) = '#skF_7'
      | r1_tarski('#skF_8',B_650) ) ),
    inference(resolution,[status(thm)],[c_14113,c_13664])).

tff(c_14197,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_14138,c_14187])).

tff(c_14204,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_14197,c_8])).

tff(c_14209,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_14187,c_14204])).

tff(c_13710,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_4'(A_22),A_22)
      | A_22 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11301,c_40])).

tff(c_15097,plain,(
    ! [A_686,B_687] : k5_xboole_0(k5_xboole_0(A_686,B_687),k2_xboole_0(A_686,B_687)) = k3_xboole_0(A_686,B_687) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_15160,plain,(
    ! [A_39] : k5_xboole_0('#skF_8',k2_xboole_0(A_39,A_39)) = k3_xboole_0(A_39,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_11302,c_15097])).

tff(c_15171,plain,(
    ! [A_39] : k5_xboole_0('#skF_8',A_39) = A_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_15160])).

tff(c_15157,plain,(
    k5_xboole_0(k5_xboole_0('#skF_8','#skF_9'),'#skF_8') = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_13581,c_15097])).

tff(c_15268,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15171,c_4,c_15171,c_15157])).

tff(c_15487,plain,(
    ! [D_696] :
      ( r2_hidden(D_696,'#skF_8')
      | ~ r2_hidden(D_696,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15268,c_16])).

tff(c_15499,plain,
    ( r2_hidden('#skF_4'('#skF_9'),'#skF_8')
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_13710,c_15487])).

tff(c_15505,plain,(
    r2_hidden('#skF_4'('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_13579,c_15499])).

tff(c_15512,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_15505,c_13664])).

tff(c_15518,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_15512,c_13710])).

tff(c_15522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13579,c_14209,c_15518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.02/2.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.14/2.88  
% 8.14/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.14/2.89  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 8.14/2.89  
% 8.14/2.89  %Foreground sorts:
% 8.14/2.89  
% 8.14/2.89  
% 8.14/2.89  %Background operators:
% 8.14/2.89  
% 8.14/2.89  
% 8.14/2.89  %Foreground operators:
% 8.14/2.89  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 8.14/2.89  tff('#skF_4', type, '#skF_4': $i > $i).
% 8.14/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.14/2.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.14/2.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.14/2.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.14/2.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.14/2.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.14/2.89  tff('#skF_7', type, '#skF_7': $i).
% 8.14/2.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.14/2.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.14/2.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.14/2.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.14/2.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.14/2.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.14/2.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.14/2.89  tff('#skF_9', type, '#skF_9': $i).
% 8.14/2.89  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 8.14/2.89  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.14/2.89  tff('#skF_8', type, '#skF_8': $i).
% 8.14/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.14/2.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.14/2.89  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.14/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.14/2.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.14/2.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.14/2.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.14/2.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.14/2.89  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.14/2.89  
% 8.26/2.92  tff(f_137, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 8.26/2.92  tff(f_116, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 8.26/2.92  tff(f_85, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.26/2.92  tff(f_70, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.26/2.92  tff(f_64, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.26/2.92  tff(f_89, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.26/2.92  tff(f_56, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.26/2.92  tff(f_54, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 8.26/2.92  tff(f_91, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.26/2.92  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.26/2.92  tff(f_72, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.26/2.92  tff(f_87, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.26/2.92  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.26/2.92  tff(f_81, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.26/2.92  tff(f_45, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.26/2.92  tff(f_98, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 8.26/2.92  tff(f_83, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 8.26/2.92  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.26/2.92  tff(c_98, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.26/2.92  tff(c_141, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_98])).
% 8.26/2.92  tff(c_92, plain, (![A_75, B_76]: (r1_tarski(k1_tarski(A_75), B_76) | ~r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.26/2.92  tff(c_96, plain, (k1_xboole_0!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.26/2.92  tff(c_146, plain, (k1_tarski('#skF_7')!='#skF_8'), inference(splitLeft, [status(thm)], [c_96])).
% 8.26/2.92  tff(c_102, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.26/2.92  tff(c_147, plain, (![A_86, B_87]: (r1_tarski(A_86, k2_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.26/2.92  tff(c_150, plain, (r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_147])).
% 8.26/2.92  tff(c_507, plain, (![B_127, A_128]: (B_127=A_128 | ~r1_tarski(B_127, A_128) | ~r1_tarski(A_128, B_127))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.26/2.92  tff(c_515, plain, (k1_tarski('#skF_7')='#skF_8' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_150, c_507])).
% 8.26/2.92  tff(c_525, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_146, c_515])).
% 8.26/2.92  tff(c_534, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_92, c_525])).
% 8.26/2.92  tff(c_40, plain, (![A_22]: (r2_hidden('#skF_4'(A_22), A_22) | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.26/2.92  tff(c_60, plain, (![A_39]: (k5_xboole_0(A_39, A_39)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.26/2.92  tff(c_38, plain, (![A_20]: (k3_xboole_0(A_20, A_20)=A_20)), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.26/2.92  tff(c_36, plain, (![A_18]: (k2_xboole_0(A_18, A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.26/2.92  tff(c_7348, plain, (![A_350, B_351]: (k5_xboole_0(k5_xboole_0(A_350, B_351), k2_xboole_0(A_350, B_351))=k3_xboole_0(A_350, B_351))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.26/2.92  tff(c_7448, plain, (![A_18]: (k5_xboole_0(k5_xboole_0(A_18, A_18), A_18)=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_36, c_7348])).
% 8.26/2.92  tff(c_7465, plain, (![A_352]: (k5_xboole_0(k1_xboole_0, A_352)=A_352)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_38, c_7448])).
% 8.26/2.92  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.26/2.92  tff(c_7503, plain, (![A_352]: (k5_xboole_0(A_352, k1_xboole_0)=A_352)), inference(superposition, [status(thm), theory('equality')], [c_7465, c_4])).
% 8.26/2.92  tff(c_48, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.26/2.92  tff(c_1395, plain, (![A_159, B_160, C_161]: (k5_xboole_0(k5_xboole_0(A_159, B_160), C_161)=k5_xboole_0(A_159, k5_xboole_0(B_160, C_161)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.26/2.92  tff(c_1176, plain, (![A_154, B_155]: (k5_xboole_0(k5_xboole_0(A_154, B_155), k2_xboole_0(A_154, B_155))=k3_xboole_0(A_154, B_155))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.26/2.92  tff(c_1242, plain, (k5_xboole_0(k5_xboole_0('#skF_8', '#skF_9'), k1_tarski('#skF_7'))=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_102, c_1176])).
% 8.26/2.92  tff(c_1404, plain, (k5_xboole_0('#skF_8', k5_xboole_0('#skF_9', k1_tarski('#skF_7')))=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1395, c_1242])).
% 8.26/2.92  tff(c_1245, plain, (![A_18]: (k5_xboole_0(k5_xboole_0(A_18, A_18), A_18)=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1176])).
% 8.26/2.92  tff(c_1255, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, A_18)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_60, c_1245])).
% 8.26/2.92  tff(c_1481, plain, (![A_39, C_161]: (k5_xboole_0(A_39, k5_xboole_0(A_39, C_161))=k5_xboole_0(k1_xboole_0, C_161))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1395])).
% 8.26/2.92  tff(c_1494, plain, (![A_39, C_161]: (k5_xboole_0(A_39, k5_xboole_0(A_39, C_161))=C_161)), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_1481])).
% 8.26/2.92  tff(c_1664, plain, (k5_xboole_0('#skF_9', k1_tarski('#skF_7'))=k5_xboole_0('#skF_8', k3_xboole_0('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1404, c_1494])).
% 8.26/2.92  tff(c_1673, plain, (k5_xboole_0('#skF_9', k1_tarski('#skF_7'))=k4_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1664])).
% 8.26/2.92  tff(c_1495, plain, (![A_162, C_163]: (k5_xboole_0(A_162, k5_xboole_0(A_162, C_163))=C_163)), inference(demodulation, [status(thm), theory('equality')], [c_1255, c_1481])).
% 8.26/2.92  tff(c_1550, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1495])).
% 8.26/2.92  tff(c_1928, plain, (k5_xboole_0(k1_tarski('#skF_7'), k4_xboole_0('#skF_8', '#skF_9'))='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_1673, c_1550])).
% 8.26/2.92  tff(c_155, plain, (![B_88, A_89]: (k2_xboole_0(B_88, A_89)=k2_xboole_0(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.26/2.92  tff(c_56, plain, (![A_34, B_35]: (r1_tarski(A_34, k2_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.26/2.92  tff(c_195, plain, (![A_91, B_92]: (r1_tarski(A_91, k2_xboole_0(B_92, A_91)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_56])).
% 8.26/2.92  tff(c_204, plain, (r1_tarski('#skF_9', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_195])).
% 8.26/2.92  tff(c_343, plain, (![A_114, B_115]: (k2_xboole_0(A_114, B_115)=B_115 | ~r1_tarski(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.26/2.92  tff(c_363, plain, (k2_xboole_0('#skF_9', k1_tarski('#skF_7'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_204, c_343])).
% 8.26/2.92  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.26/2.92  tff(c_1569, plain, (![A_164, B_165]: (k5_xboole_0(A_164, k5_xboole_0(B_165, A_164))=B_165)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1495])).
% 8.26/2.92  tff(c_1605, plain, (![A_39, C_161]: (k5_xboole_0(k5_xboole_0(A_39, C_161), C_161)=A_39)), inference(superposition, [status(thm), theory('equality')], [c_1494, c_1569])).
% 8.26/2.92  tff(c_1922, plain, (k5_xboole_0(k4_xboole_0('#skF_8', '#skF_9'), k1_tarski('#skF_7'))='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_1673, c_1605])).
% 8.26/2.92  tff(c_1975, plain, (k5_xboole_0(k1_tarski('#skF_7'), '#skF_9')=k4_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1922, c_1550])).
% 8.26/2.92  tff(c_62, plain, (![A_40, B_41]: (k5_xboole_0(k5_xboole_0(A_40, B_41), k2_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.26/2.92  tff(c_2110, plain, (k5_xboole_0(k4_xboole_0('#skF_8', '#skF_9'), k2_xboole_0(k1_tarski('#skF_7'), '#skF_9'))=k3_xboole_0(k1_tarski('#skF_7'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1975, c_62])).
% 8.26/2.92  tff(c_2129, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1928, c_4, c_363, c_2, c_2110])).
% 8.26/2.92  tff(c_16, plain, (![D_15, A_10, B_11]: (r2_hidden(D_15, A_10) | ~r2_hidden(D_15, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.26/2.92  tff(c_2194, plain, (![D_179]: (r2_hidden(D_179, k1_tarski('#skF_7')) | ~r2_hidden(D_179, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2129, c_16])).
% 8.26/2.92  tff(c_64, plain, (![C_46, A_42]: (C_46=A_42 | ~r2_hidden(C_46, k1_tarski(A_42)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.26/2.92  tff(c_2207, plain, (![D_180]: (D_180='#skF_7' | ~r2_hidden(D_180, '#skF_9'))), inference(resolution, [status(thm)], [c_2194, c_64])).
% 8.26/2.92  tff(c_2217, plain, ('#skF_4'('#skF_9')='#skF_7' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_40, c_2207])).
% 8.26/2.92  tff(c_2218, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_2217])).
% 8.26/2.92  tff(c_2226, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_141])).
% 8.26/2.92  tff(c_2225, plain, (![A_22]: (r2_hidden('#skF_4'(A_22), A_22) | A_22='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_40])).
% 8.26/2.92  tff(c_365, plain, (k2_xboole_0('#skF_8', k1_tarski('#skF_7'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_150, c_343])).
% 8.26/2.92  tff(c_435, plain, (![A_122, B_123]: (k2_xboole_0(A_122, k2_xboole_0(A_122, B_123))=k2_xboole_0(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.26/2.92  tff(c_469, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_435])).
% 8.26/2.92  tff(c_170, plain, (![A_89, B_88]: (r1_tarski(A_89, k2_xboole_0(B_88, A_89)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_56])).
% 8.26/2.92  tff(c_827, plain, (![A_145, B_146]: (k2_xboole_0(A_145, k2_xboole_0(B_146, A_145))=k2_xboole_0(B_146, A_145))), inference(resolution, [status(thm)], [c_170, c_343])).
% 8.26/2.92  tff(c_901, plain, (![B_2, A_1]: (k2_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_827])).
% 8.26/2.92  tff(c_1045, plain, (![B_152, A_153]: (k2_xboole_0(B_152, k2_xboole_0(B_152, A_153))=k2_xboole_0(A_153, B_152))), inference(superposition, [status(thm), theory('equality')], [c_2, c_827])).
% 8.26/2.92  tff(c_1094, plain, (![B_2, A_1]: (k2_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k2_xboole_0(B_2, k2_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_901, c_1045])).
% 8.26/2.92  tff(c_3770, plain, (![B_237, A_238]: (k2_xboole_0(k2_xboole_0(B_237, A_238), B_237)=k2_xboole_0(B_237, A_238))), inference(demodulation, [status(thm), theory('equality')], [c_469, c_1094])).
% 8.26/2.92  tff(c_3791, plain, (![B_237, A_238]: (k5_xboole_0(k5_xboole_0(k2_xboole_0(B_237, A_238), B_237), k2_xboole_0(B_237, A_238))=k3_xboole_0(k2_xboole_0(B_237, A_238), B_237))), inference(superposition, [status(thm), theory('equality')], [c_3770, c_62])).
% 8.26/2.92  tff(c_3920, plain, (![B_239, A_240]: (k3_xboole_0(k2_xboole_0(B_239, A_240), B_239)=B_239)), inference(demodulation, [status(thm), theory('equality')], [c_1550, c_4, c_4, c_3791])).
% 8.26/2.92  tff(c_3971, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_365, c_3920])).
% 8.26/2.92  tff(c_4201, plain, (![D_246]: (r2_hidden(D_246, k1_tarski('#skF_7')) | ~r2_hidden(D_246, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3971, c_16])).
% 8.26/2.92  tff(c_4246, plain, (![D_250]: (D_250='#skF_7' | ~r2_hidden(D_250, '#skF_8'))), inference(resolution, [status(thm)], [c_4201, c_64])).
% 8.26/2.92  tff(c_4262, plain, ('#skF_4'('#skF_8')='#skF_7' | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_2225, c_4246])).
% 8.26/2.92  tff(c_4279, plain, ('#skF_4'('#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_2226, c_4262])).
% 8.26/2.92  tff(c_4286, plain, (r2_hidden('#skF_7', '#skF_8') | '#skF_9'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_4279, c_2225])).
% 8.26/2.92  tff(c_4290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2226, c_534, c_4286])).
% 8.26/2.92  tff(c_4292, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_2217])).
% 8.26/2.92  tff(c_521, plain, (k1_tarski('#skF_7')='#skF_9' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_9')), inference(resolution, [status(thm)], [c_204, c_507])).
% 8.26/2.92  tff(c_549, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_521])).
% 8.26/2.92  tff(c_553, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_92, c_549])).
% 8.26/2.92  tff(c_4291, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_2217])).
% 8.26/2.92  tff(c_4339, plain, (r2_hidden('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_4291, c_40])).
% 8.26/2.92  tff(c_4343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4292, c_553, c_4339])).
% 8.26/2.92  tff(c_4344, plain, (k1_tarski('#skF_7')='#skF_9'), inference(splitRight, [status(thm)], [c_521])).
% 8.26/2.92  tff(c_4352, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4344, c_102])).
% 8.26/2.92  tff(c_7421, plain, (k5_xboole_0(k5_xboole_0('#skF_8', '#skF_9'), '#skF_9')=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_4352, c_7348])).
% 8.26/2.92  tff(c_58, plain, (![A_36, B_37, C_38]: (k5_xboole_0(k5_xboole_0(A_36, B_37), C_38)=k5_xboole_0(A_36, k5_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.26/2.92  tff(c_7630, plain, (k5_xboole_0('#skF_8', k5_xboole_0('#skF_9', '#skF_9'))=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_7421, c_58])).
% 8.26/2.92  tff(c_7649, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7503, c_60, c_7630])).
% 8.26/2.92  tff(c_14, plain, (![D_15, B_11, A_10]: (r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.26/2.92  tff(c_8169, plain, (![D_369]: (r2_hidden(D_369, '#skF_9') | ~r2_hidden(D_369, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_7649, c_14])).
% 8.26/2.92  tff(c_4376, plain, (![C_46]: (C_46='#skF_7' | ~r2_hidden(C_46, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4344, c_64])).
% 8.26/2.92  tff(c_8200, plain, (![D_370]: (D_370='#skF_7' | ~r2_hidden(D_370, '#skF_8'))), inference(resolution, [status(thm)], [c_8169, c_4376])).
% 8.26/2.92  tff(c_8212, plain, ('#skF_4'('#skF_8')='#skF_7' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_40, c_8200])).
% 8.26/2.92  tff(c_8217, plain, ('#skF_4'('#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_141, c_8212])).
% 8.26/2.92  tff(c_8260, plain, (r2_hidden('#skF_7', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_8217, c_40])).
% 8.26/2.92  tff(c_8264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_534, c_8260])).
% 8.26/2.92  tff(c_8265, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_96])).
% 8.26/2.92  tff(c_8266, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_96])).
% 8.26/2.92  tff(c_100, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.26/2.92  tff(c_8276, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8266, c_8266, c_100])).
% 8.26/2.92  tff(c_8267, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8266, c_102])).
% 8.26/2.92  tff(c_8290, plain, (![B_376, A_377]: (k2_xboole_0(B_376, A_377)=k2_xboole_0(A_377, B_376))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.26/2.92  tff(c_8329, plain, (![A_378, B_379]: (r1_tarski(A_378, k2_xboole_0(B_379, A_378)))), inference(superposition, [status(thm), theory('equality')], [c_8290, c_56])).
% 8.26/2.92  tff(c_8338, plain, (r1_tarski('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_8267, c_8329])).
% 8.26/2.92  tff(c_8756, plain, (![B_418, A_419]: (B_418=A_419 | ~r1_tarski(B_418, A_419) | ~r1_tarski(A_419, B_418))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.26/2.92  tff(c_8760, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_8338, c_8756])).
% 8.26/2.92  tff(c_8770, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_8276, c_8760])).
% 8.26/2.92  tff(c_8818, plain, (![A_427, B_428]: (r2_hidden('#skF_1'(A_427, B_428), A_427) | r1_tarski(A_427, B_428))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.26/2.92  tff(c_8348, plain, (![C_383, A_384]: (C_383=A_384 | ~r2_hidden(C_383, k1_tarski(A_384)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.26/2.92  tff(c_8355, plain, (![C_383]: (C_383='#skF_7' | ~r2_hidden(C_383, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8266, c_8348])).
% 8.26/2.92  tff(c_8840, plain, (![B_429]: ('#skF_1'('#skF_8', B_429)='#skF_7' | r1_tarski('#skF_8', B_429))), inference(resolution, [status(thm)], [c_8818, c_8355])).
% 8.26/2.92  tff(c_8856, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_8840, c_8770])).
% 8.26/2.92  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.26/2.92  tff(c_8866, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_8856, c_8])).
% 8.26/2.92  tff(c_8871, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_8770, c_8866])).
% 8.26/2.92  tff(c_10313, plain, (![A_470, B_471]: (k5_xboole_0(k5_xboole_0(A_470, B_471), k2_xboole_0(A_470, B_471))=k3_xboole_0(A_470, B_471))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.26/2.92  tff(c_10382, plain, (![A_18]: (k5_xboole_0(k5_xboole_0(A_18, A_18), A_18)=k3_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_36, c_10313])).
% 8.26/2.92  tff(c_10394, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, A_18)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_38, c_10382])).
% 8.26/2.92  tff(c_10534, plain, (![A_475, B_476, C_477]: (k5_xboole_0(k5_xboole_0(A_475, B_476), C_477)=k5_xboole_0(A_475, k5_xboole_0(B_476, C_477)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.26/2.92  tff(c_10620, plain, (![A_39, C_477]: (k5_xboole_0(A_39, k5_xboole_0(A_39, C_477))=k5_xboole_0(k1_xboole_0, C_477))), inference(superposition, [status(thm), theory('equality')], [c_60, c_10534])).
% 8.26/2.92  tff(c_10636, plain, (![A_478, C_479]: (k5_xboole_0(A_478, k5_xboole_0(A_478, C_479))=C_479)), inference(demodulation, [status(thm), theory('equality')], [c_10394, c_10620])).
% 8.26/2.92  tff(c_10710, plain, (![A_480, B_481]: (k5_xboole_0(A_480, k5_xboole_0(B_481, A_480))=B_481)), inference(superposition, [status(thm), theory('equality')], [c_4, c_10636])).
% 8.26/2.92  tff(c_10691, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_10636])).
% 8.26/2.92  tff(c_10713, plain, (![B_481, A_480]: (k5_xboole_0(k5_xboole_0(B_481, A_480), B_481)=A_480)), inference(superposition, [status(thm), theory('equality')], [c_10710, c_10691])).
% 8.26/2.92  tff(c_10379, plain, (k5_xboole_0(k5_xboole_0('#skF_8', '#skF_9'), '#skF_8')=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_8267, c_10313])).
% 8.26/2.92  tff(c_10893, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_10713, c_10379])).
% 8.26/2.92  tff(c_11258, plain, (![D_494]: (r2_hidden(D_494, '#skF_8') | ~r2_hidden(D_494, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_10893, c_16])).
% 8.26/2.92  tff(c_11274, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_40, c_11258])).
% 8.26/2.92  tff(c_11282, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_8265, c_11274])).
% 8.26/2.92  tff(c_11289, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_11282, c_8355])).
% 8.26/2.92  tff(c_11295, plain, (r2_hidden('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_11289, c_40])).
% 8.26/2.92  tff(c_11299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8265, c_8871, c_11295])).
% 8.26/2.92  tff(c_11301, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_98])).
% 8.26/2.92  tff(c_11318, plain, ('#skF_9'!='#skF_8' | k1_tarski('#skF_7')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11301, c_96])).
% 8.26/2.92  tff(c_11319, plain, (k1_tarski('#skF_7')!='#skF_8'), inference(splitLeft, [status(thm)], [c_11318])).
% 8.26/2.92  tff(c_11302, plain, (![A_39]: (k5_xboole_0(A_39, A_39)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11301, c_60])).
% 8.26/2.92  tff(c_11367, plain, (![A_22]: (r2_hidden('#skF_4'(A_22), A_22) | A_22='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11301, c_40])).
% 8.26/2.92  tff(c_12548, plain, (![A_571, B_572]: (k5_xboole_0(k5_xboole_0(A_571, B_572), k2_xboole_0(A_571, B_572))=k3_xboole_0(A_571, B_572))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.26/2.92  tff(c_12645, plain, (![A_39]: (k5_xboole_0('#skF_8', k2_xboole_0(A_39, A_39))=k3_xboole_0(A_39, A_39))), inference(superposition, [status(thm), theory('equality')], [c_11302, c_12548])).
% 8.26/2.92  tff(c_12655, plain, (![A_39]: (k5_xboole_0('#skF_8', A_39)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_12645])).
% 8.26/2.92  tff(c_12642, plain, (k5_xboole_0(k5_xboole_0('#skF_8', '#skF_9'), k1_tarski('#skF_7'))=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_102, c_12548])).
% 8.26/2.92  tff(c_12813, plain, (k5_xboole_0('#skF_9', k1_tarski('#skF_7'))=k3_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12655, c_12642])).
% 8.26/2.92  tff(c_12223, plain, (![A_562, B_563, C_564]: (k5_xboole_0(k5_xboole_0(A_562, B_563), C_564)=k5_xboole_0(A_562, k5_xboole_0(B_563, C_564)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.26/2.92  tff(c_12273, plain, (![A_39, C_564]: (k5_xboole_0(A_39, k5_xboole_0(A_39, C_564))=k5_xboole_0('#skF_8', C_564))), inference(superposition, [status(thm), theory('equality')], [c_11302, c_12223])).
% 8.26/2.92  tff(c_12831, plain, (![A_575, C_576]: (k5_xboole_0(A_575, k5_xboole_0(A_575, C_576))=C_576)), inference(demodulation, [status(thm), theory('equality')], [c_12655, c_12273])).
% 8.26/2.92  tff(c_12959, plain, (![B_582, A_583]: (k5_xboole_0(B_582, k5_xboole_0(A_583, B_582))=A_583)), inference(superposition, [status(thm), theory('equality')], [c_4, c_12831])).
% 8.26/2.92  tff(c_13002, plain, (k5_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_8', '#skF_9'))='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_12813, c_12959])).
% 8.26/2.92  tff(c_11374, plain, (![B_503, A_504]: (k2_xboole_0(B_503, A_504)=k2_xboole_0(A_504, B_503))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.26/2.92  tff(c_11413, plain, (![A_505, B_506]: (r1_tarski(A_505, k2_xboole_0(B_506, A_505)))), inference(superposition, [status(thm), theory('equality')], [c_11374, c_56])).
% 8.26/2.92  tff(c_11422, plain, (r1_tarski('#skF_9', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_11413])).
% 8.26/2.92  tff(c_11477, plain, (![A_518, B_519]: (k2_xboole_0(A_518, B_519)=B_519 | ~r1_tarski(A_518, B_519))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.26/2.92  tff(c_11497, plain, (k2_xboole_0('#skF_9', k1_tarski('#skF_7'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_11422, c_11477])).
% 8.26/2.92  tff(c_12657, plain, (![A_39, C_564]: (k5_xboole_0(A_39, k5_xboole_0(A_39, C_564))=C_564)), inference(demodulation, [status(thm), theory('equality')], [c_12655, c_12273])).
% 8.26/2.92  tff(c_13375, plain, (k5_xboole_0(k1_tarski('#skF_7'), '#skF_9')=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_13002, c_12657])).
% 8.26/2.92  tff(c_13405, plain, (k5_xboole_0(k3_xboole_0('#skF_8', '#skF_9'), k2_xboole_0(k1_tarski('#skF_7'), '#skF_9'))=k3_xboole_0(k1_tarski('#skF_7'), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_13375, c_62])).
% 8.26/2.92  tff(c_13426, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_13002, c_4, c_11497, c_2, c_13405])).
% 8.26/2.92  tff(c_13520, plain, (![D_595]: (r2_hidden(D_595, k1_tarski('#skF_7')) | ~r2_hidden(D_595, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_13426, c_16])).
% 8.26/2.92  tff(c_13533, plain, (![D_596]: (D_596='#skF_7' | ~r2_hidden(D_596, '#skF_9'))), inference(resolution, [status(thm)], [c_13520, c_64])).
% 8.26/2.92  tff(c_13548, plain, ('#skF_4'('#skF_9')='#skF_7' | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_11367, c_13533])).
% 8.26/2.92  tff(c_13549, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_13548])).
% 8.26/2.92  tff(c_12907, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k5_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_12831])).
% 8.26/2.92  tff(c_13372, plain, (k5_xboole_0(k3_xboole_0('#skF_8', '#skF_9'), '#skF_9')=k1_tarski('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_13002, c_12907])).
% 8.26/2.92  tff(c_13553, plain, (k5_xboole_0(k3_xboole_0('#skF_8', '#skF_8'), '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13549, c_13549, c_13372])).
% 8.26/2.92  tff(c_13566, plain, (k1_tarski('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11302, c_38, c_13553])).
% 8.26/2.92  tff(c_13568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11319, c_13566])).
% 8.26/2.92  tff(c_13570, plain, ('#skF_9'!='#skF_8'), inference(splitRight, [status(thm)], [c_13548])).
% 8.26/2.92  tff(c_11300, plain, (k1_tarski('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_98])).
% 8.26/2.92  tff(c_11596, plain, (![B_529, A_530]: (B_529=A_530 | ~r1_tarski(B_529, A_530) | ~r1_tarski(A_530, B_529))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.26/2.92  tff(c_11600, plain, (k1_tarski('#skF_7')='#skF_9' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_9')), inference(resolution, [status(thm)], [c_11422, c_11596])).
% 8.26/2.92  tff(c_11612, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_11300, c_11600])).
% 8.26/2.92  tff(c_11629, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_92, c_11612])).
% 8.26/2.92  tff(c_13569, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_13548])).
% 8.26/2.92  tff(c_13574, plain, (r2_hidden('#skF_7', '#skF_9') | '#skF_9'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_13569, c_11367])).
% 8.26/2.92  tff(c_13578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13570, c_11629, c_13574])).
% 8.26/2.92  tff(c_13579, plain, ('#skF_9'!='#skF_8'), inference(splitRight, [status(thm)], [c_11318])).
% 8.26/2.92  tff(c_13580, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_11318])).
% 8.26/2.92  tff(c_13581, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_13580, c_102])).
% 8.26/2.92  tff(c_13605, plain, (![B_599, A_600]: (k2_xboole_0(B_599, A_600)=k2_xboole_0(A_600, B_599))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.26/2.92  tff(c_13644, plain, (![A_601, B_602]: (r1_tarski(A_601, k2_xboole_0(B_602, A_601)))), inference(superposition, [status(thm), theory('equality')], [c_13605, c_56])).
% 8.26/2.92  tff(c_13653, plain, (r1_tarski('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_13581, c_13644])).
% 8.26/2.92  tff(c_14170, plain, (![B_653, A_654]: (B_653=A_654 | ~r1_tarski(B_653, A_654) | ~r1_tarski(A_654, B_653))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.26/2.92  tff(c_14176, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_13653, c_14170])).
% 8.26/2.92  tff(c_14187, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_13579, c_14176])).
% 8.26/2.92  tff(c_14113, plain, (![A_649, B_650]: (r2_hidden('#skF_1'(A_649, B_650), A_649) | r1_tarski(A_649, B_650))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.26/2.92  tff(c_13661, plain, (![C_603, A_604]: (C_603=A_604 | ~r2_hidden(C_603, k1_tarski(A_604)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.26/2.92  tff(c_13664, plain, (![C_603]: (C_603='#skF_7' | ~r2_hidden(C_603, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_13580, c_13661])).
% 8.26/2.92  tff(c_14138, plain, (![B_650]: ('#skF_1'('#skF_8', B_650)='#skF_7' | r1_tarski('#skF_8', B_650))), inference(resolution, [status(thm)], [c_14113, c_13664])).
% 8.26/2.92  tff(c_14197, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_14138, c_14187])).
% 8.26/2.92  tff(c_14204, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_14197, c_8])).
% 8.26/2.92  tff(c_14209, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_14187, c_14204])).
% 8.26/2.92  tff(c_13710, plain, (![A_22]: (r2_hidden('#skF_4'(A_22), A_22) | A_22='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11301, c_40])).
% 8.26/2.92  tff(c_15097, plain, (![A_686, B_687]: (k5_xboole_0(k5_xboole_0(A_686, B_687), k2_xboole_0(A_686, B_687))=k3_xboole_0(A_686, B_687))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.26/2.92  tff(c_15160, plain, (![A_39]: (k5_xboole_0('#skF_8', k2_xboole_0(A_39, A_39))=k3_xboole_0(A_39, A_39))), inference(superposition, [status(thm), theory('equality')], [c_11302, c_15097])).
% 8.26/2.92  tff(c_15171, plain, (![A_39]: (k5_xboole_0('#skF_8', A_39)=A_39)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_15160])).
% 8.26/2.92  tff(c_15157, plain, (k5_xboole_0(k5_xboole_0('#skF_8', '#skF_9'), '#skF_8')=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_13581, c_15097])).
% 8.26/2.92  tff(c_15268, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_15171, c_4, c_15171, c_15157])).
% 8.26/2.92  tff(c_15487, plain, (![D_696]: (r2_hidden(D_696, '#skF_8') | ~r2_hidden(D_696, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_15268, c_16])).
% 8.26/2.92  tff(c_15499, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8') | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_13710, c_15487])).
% 8.26/2.92  tff(c_15505, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_13579, c_15499])).
% 8.26/2.92  tff(c_15512, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_15505, c_13664])).
% 8.26/2.92  tff(c_15518, plain, (r2_hidden('#skF_7', '#skF_9') | '#skF_9'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_15512, c_13710])).
% 8.26/2.92  tff(c_15522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13579, c_14209, c_15518])).
% 8.26/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.26/2.92  
% 8.26/2.92  Inference rules
% 8.26/2.92  ----------------------
% 8.26/2.92  #Ref     : 0
% 8.26/2.92  #Sup     : 3711
% 8.26/2.92  #Fact    : 0
% 8.26/2.92  #Define  : 0
% 8.26/2.92  #Split   : 7
% 8.26/2.92  #Chain   : 0
% 8.26/2.92  #Close   : 0
% 8.26/2.92  
% 8.26/2.92  Ordering : KBO
% 8.26/2.92  
% 8.26/2.92  Simplification rules
% 8.26/2.92  ----------------------
% 8.26/2.92  #Subsume      : 273
% 8.26/2.92  #Demod        : 2622
% 8.26/2.92  #Tautology    : 2287
% 8.26/2.92  #SimpNegUnit  : 45
% 8.26/2.92  #BackRed      : 63
% 8.26/2.92  
% 8.26/2.92  #Partial instantiations: 0
% 8.26/2.92  #Strategies tried      : 1
% 8.26/2.92  
% 8.26/2.92  Timing (in seconds)
% 8.26/2.92  ----------------------
% 8.26/2.92  Preprocessing        : 0.37
% 8.26/2.92  Parsing              : 0.19
% 8.26/2.92  CNF conversion       : 0.03
% 8.26/2.92  Main loop            : 1.75
% 8.26/2.92  Inferencing          : 0.52
% 8.26/2.92  Reduction            : 0.77
% 8.26/2.92  Demodulation         : 0.61
% 8.26/2.92  BG Simplification    : 0.06
% 8.26/2.92  Subsumption          : 0.28
% 8.26/2.92  Abstraction          : 0.08
% 8.26/2.92  MUC search           : 0.00
% 8.26/2.92  Cooper               : 0.00
% 8.26/2.92  Total                : 2.18
% 8.26/2.92  Index Insertion      : 0.00
% 8.26/2.92  Index Deletion       : 0.00
% 8.26/2.92  Index Matching       : 0.00
% 8.26/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
