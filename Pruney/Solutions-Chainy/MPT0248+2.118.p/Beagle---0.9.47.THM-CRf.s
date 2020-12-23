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
% DateTime   : Thu Dec  3 09:50:20 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 164 expanded)
%              Number of leaves         :   37 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  130 ( 342 expanded)
%              Number of equality atoms :   73 ( 275 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_78,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_106,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_76,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_94,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_44,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_110,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_44])).

tff(c_1151,plain,(
    ! [B_156,A_157] :
      ( k1_tarski(B_156) = A_157
      | k1_xboole_0 = A_157
      | ~ r1_tarski(A_157,k1_tarski(B_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1162,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_110,c_1151])).

tff(c_1174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_94,c_1162])).

tff(c_1175,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1176,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1316,plain,(
    ! [A_177,B_178] :
      ( k4_xboole_0(A_177,B_178) = '#skF_7'
      | ~ r1_tarski(A_177,B_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1176,c_28])).

tff(c_1332,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_44,c_1316])).

tff(c_34,plain,(
    ! [A_17,B_18] : k3_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1507,plain,(
    ! [A_198,B_199] : k5_xboole_0(A_198,k3_xboole_0(A_198,B_199)) = k4_xboole_0(A_198,B_199) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1522,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k5_xboole_0(A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1507])).

tff(c_1527,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1522])).

tff(c_72,plain,(
    ! [B_39] : r1_tarski(k1_xboole_0,k1_tarski(B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1178,plain,(
    ! [B_39] : r1_tarski('#skF_7',k1_tarski(B_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1176,c_72])).

tff(c_1401,plain,(
    ! [A_192,B_193] :
      ( k2_xboole_0(A_192,B_193) = B_193
      | ~ r1_tarski(A_192,B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1426,plain,(
    ! [B_194] : k2_xboole_0('#skF_7',k1_tarski(B_194)) = k1_tarski(B_194) ),
    inference(resolution,[status(thm)],[c_1178,c_1401])).

tff(c_1435,plain,(
    ! [B_194] : k3_xboole_0('#skF_7',k1_tarski(B_194)) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1426,c_34])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1395,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1176,c_22])).

tff(c_1609,plain,(
    ! [A_212,C_213,B_214] :
      ( r1_xboole_0(A_212,C_213)
      | ~ r1_xboole_0(A_212,k2_xboole_0(B_214,C_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1627,plain,(
    ! [A_215] :
      ( r1_xboole_0(A_215,'#skF_8')
      | ~ r1_xboole_0(A_215,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1609])).

tff(c_2455,plain,(
    ! [A_3407] :
      ( r1_xboole_0(A_3407,'#skF_8')
      | k3_xboole_0(A_3407,k1_tarski('#skF_6')) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1395,c_1627])).

tff(c_2464,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1435,c_2455])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1393,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = '#skF_7'
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1176,c_20])).

tff(c_2468,plain,(
    k3_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2464,c_1393])).

tff(c_30,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2472,plain,(
    k5_xboole_0('#skF_7','#skF_7') = k4_xboole_0('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2468,c_30])).

tff(c_2475,plain,(
    k4_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1527,c_2472])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1382,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1176,c_26])).

tff(c_2690,plain,(
    ! [A_3416,B_3417] :
      ( k2_xboole_0(A_3416,B_3417) = B_3417
      | k4_xboole_0(A_3416,B_3417) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1382,c_1401])).

tff(c_2710,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2475,c_2690])).

tff(c_2718,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2710,c_82])).

tff(c_2720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1175,c_2718])).

tff(c_2722,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2757,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2722,c_2722,c_80])).

tff(c_2721,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_24,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2727,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2722,c_82])).

tff(c_3578,plain,(
    ! [D_3486,B_3487,A_3488] :
      ( ~ r2_hidden(D_3486,B_3487)
      | r2_hidden(D_3486,k2_xboole_0(A_3488,B_3487)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3608,plain,(
    ! [D_3489] :
      ( ~ r2_hidden(D_3489,'#skF_8')
      | r2_hidden(D_3489,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2727,c_3578])).

tff(c_2767,plain,(
    ! [C_3422,A_3423] :
      ( C_3422 = A_3423
      | ~ r2_hidden(C_3422,k1_tarski(A_3423)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2770,plain,(
    ! [C_3422] :
      ( C_3422 = '#skF_6'
      | ~ r2_hidden(C_3422,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2722,c_2767])).

tff(c_3619,plain,(
    ! [D_3490] :
      ( D_3490 = '#skF_6'
      | ~ r2_hidden(D_3490,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3608,c_2770])).

tff(c_3627,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_24,c_3619])).

tff(c_3632,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_2721,c_3627])).

tff(c_3636,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_3632,c_24])).

tff(c_3639,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2721,c_3636])).

tff(c_2864,plain,(
    ! [A_3437,B_3438] :
      ( r1_tarski(k1_tarski(A_3437),B_3438)
      | ~ r2_hidden(A_3437,B_3438) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2870,plain,(
    ! [B_3438] :
      ( r1_tarski('#skF_7',B_3438)
      | ~ r2_hidden('#skF_6',B_3438) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2722,c_2864])).

tff(c_3649,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_3639,c_2870])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3657,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3649,c_32])).

tff(c_3662,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3657,c_2727])).

tff(c_3664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2757,c_3662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.92  
% 4.46/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.92  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 4.84/1.92  
% 4.84/1.92  %Foreground sorts:
% 4.84/1.92  
% 4.84/1.92  
% 4.84/1.92  %Background operators:
% 4.84/1.92  
% 4.84/1.92  
% 4.84/1.92  %Foreground operators:
% 4.84/1.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.84/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.84/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.84/1.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.84/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.84/1.92  tff('#skF_7', type, '#skF_7': $i).
% 4.84/1.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.84/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.84/1.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.84/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.84/1.92  tff('#skF_6', type, '#skF_6': $i).
% 4.84/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.84/1.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.84/1.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.84/1.92  tff('#skF_8', type, '#skF_8': $i).
% 4.84/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/1.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.84/1.92  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.84/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.84/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.84/1.92  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.84/1.92  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.84/1.92  
% 4.84/1.94  tff(f_122, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.84/1.94  tff(f_78, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.84/1.94  tff(f_101, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.84/1.94  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.84/1.94  tff(f_58, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.84/1.94  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.84/1.94  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.84/1.94  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.84/1.94  tff(f_76, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.84/1.94  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.84/1.94  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.84/1.94  tff(f_85, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.84/1.94  tff(f_95, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.84/1.94  tff(c_78, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.84/1.94  tff(c_106, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_78])).
% 4.84/1.94  tff(c_76, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.84/1.94  tff(c_94, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_76])).
% 4.84/1.94  tff(c_82, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.84/1.94  tff(c_44, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.84/1.94  tff(c_110, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_44])).
% 4.84/1.94  tff(c_1151, plain, (![B_156, A_157]: (k1_tarski(B_156)=A_157 | k1_xboole_0=A_157 | ~r1_tarski(A_157, k1_tarski(B_156)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.84/1.94  tff(c_1162, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_110, c_1151])).
% 4.84/1.94  tff(c_1174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_94, c_1162])).
% 4.84/1.94  tff(c_1175, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_78])).
% 4.84/1.94  tff(c_1176, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_78])).
% 4.84/1.94  tff(c_28, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.84/1.94  tff(c_1316, plain, (![A_177, B_178]: (k4_xboole_0(A_177, B_178)='#skF_7' | ~r1_tarski(A_177, B_178))), inference(demodulation, [status(thm), theory('equality')], [c_1176, c_28])).
% 4.84/1.94  tff(c_1332, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(A_23, B_24))='#skF_7')), inference(resolution, [status(thm)], [c_44, c_1316])).
% 4.84/1.94  tff(c_34, plain, (![A_17, B_18]: (k3_xboole_0(A_17, k2_xboole_0(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.84/1.94  tff(c_1507, plain, (![A_198, B_199]: (k5_xboole_0(A_198, k3_xboole_0(A_198, B_199))=k4_xboole_0(A_198, B_199))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.84/1.94  tff(c_1522, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k5_xboole_0(A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1507])).
% 4.84/1.94  tff(c_1527, plain, (![A_17]: (k5_xboole_0(A_17, A_17)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1522])).
% 4.84/1.94  tff(c_72, plain, (![B_39]: (r1_tarski(k1_xboole_0, k1_tarski(B_39)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.84/1.94  tff(c_1178, plain, (![B_39]: (r1_tarski('#skF_7', k1_tarski(B_39)))), inference(demodulation, [status(thm), theory('equality')], [c_1176, c_72])).
% 4.84/1.94  tff(c_1401, plain, (![A_192, B_193]: (k2_xboole_0(A_192, B_193)=B_193 | ~r1_tarski(A_192, B_193))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.84/1.94  tff(c_1426, plain, (![B_194]: (k2_xboole_0('#skF_7', k1_tarski(B_194))=k1_tarski(B_194))), inference(resolution, [status(thm)], [c_1178, c_1401])).
% 4.84/1.94  tff(c_1435, plain, (![B_194]: (k3_xboole_0('#skF_7', k1_tarski(B_194))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1426, c_34])).
% 4.84/1.94  tff(c_22, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.84/1.94  tff(c_1395, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1176, c_22])).
% 4.84/1.94  tff(c_1609, plain, (![A_212, C_213, B_214]: (r1_xboole_0(A_212, C_213) | ~r1_xboole_0(A_212, k2_xboole_0(B_214, C_213)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/1.94  tff(c_1627, plain, (![A_215]: (r1_xboole_0(A_215, '#skF_8') | ~r1_xboole_0(A_215, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1609])).
% 4.84/1.94  tff(c_2455, plain, (![A_3407]: (r1_xboole_0(A_3407, '#skF_8') | k3_xboole_0(A_3407, k1_tarski('#skF_6'))!='#skF_7')), inference(resolution, [status(thm)], [c_1395, c_1627])).
% 4.84/1.94  tff(c_2464, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1435, c_2455])).
% 4.84/1.94  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.84/1.94  tff(c_1393, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)='#skF_7' | ~r1_xboole_0(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_1176, c_20])).
% 4.84/1.94  tff(c_2468, plain, (k3_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_2464, c_1393])).
% 4.84/1.94  tff(c_30, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.84/1.94  tff(c_2472, plain, (k5_xboole_0('#skF_7', '#skF_7')=k4_xboole_0('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2468, c_30])).
% 4.84/1.94  tff(c_2475, plain, (k4_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1527, c_2472])).
% 4.84/1.94  tff(c_26, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.84/1.94  tff(c_1382, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1176, c_26])).
% 4.84/1.94  tff(c_2690, plain, (![A_3416, B_3417]: (k2_xboole_0(A_3416, B_3417)=B_3417 | k4_xboole_0(A_3416, B_3417)!='#skF_7')), inference(resolution, [status(thm)], [c_1382, c_1401])).
% 4.84/1.94  tff(c_2710, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_2475, c_2690])).
% 4.84/1.94  tff(c_2718, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2710, c_82])).
% 4.84/1.94  tff(c_2720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1175, c_2718])).
% 4.84/1.94  tff(c_2722, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_76])).
% 4.84/1.94  tff(c_80, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.84/1.94  tff(c_2757, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2722, c_2722, c_80])).
% 4.84/1.94  tff(c_2721, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_76])).
% 4.84/1.94  tff(c_24, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.84/1.94  tff(c_2727, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2722, c_82])).
% 4.84/1.94  tff(c_3578, plain, (![D_3486, B_3487, A_3488]: (~r2_hidden(D_3486, B_3487) | r2_hidden(D_3486, k2_xboole_0(A_3488, B_3487)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.84/1.94  tff(c_3608, plain, (![D_3489]: (~r2_hidden(D_3489, '#skF_8') | r2_hidden(D_3489, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2727, c_3578])).
% 4.84/1.94  tff(c_2767, plain, (![C_3422, A_3423]: (C_3422=A_3423 | ~r2_hidden(C_3422, k1_tarski(A_3423)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.84/1.94  tff(c_2770, plain, (![C_3422]: (C_3422='#skF_6' | ~r2_hidden(C_3422, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2722, c_2767])).
% 4.84/1.94  tff(c_3619, plain, (![D_3490]: (D_3490='#skF_6' | ~r2_hidden(D_3490, '#skF_8'))), inference(resolution, [status(thm)], [c_3608, c_2770])).
% 4.84/1.94  tff(c_3627, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_24, c_3619])).
% 4.84/1.94  tff(c_3632, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_2721, c_3627])).
% 4.84/1.94  tff(c_3636, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_3632, c_24])).
% 4.84/1.94  tff(c_3639, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2721, c_3636])).
% 4.84/1.94  tff(c_2864, plain, (![A_3437, B_3438]: (r1_tarski(k1_tarski(A_3437), B_3438) | ~r2_hidden(A_3437, B_3438))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.84/1.94  tff(c_2870, plain, (![B_3438]: (r1_tarski('#skF_7', B_3438) | ~r2_hidden('#skF_6', B_3438))), inference(superposition, [status(thm), theory('equality')], [c_2722, c_2864])).
% 4.84/1.94  tff(c_3649, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_3639, c_2870])).
% 4.84/1.94  tff(c_32, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.84/1.94  tff(c_3657, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_3649, c_32])).
% 4.84/1.94  tff(c_3662, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3657, c_2727])).
% 4.84/1.94  tff(c_3664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2757, c_3662])).
% 4.84/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.94  
% 4.84/1.94  Inference rules
% 4.84/1.94  ----------------------
% 4.84/1.94  #Ref     : 0
% 4.84/1.94  #Sup     : 936
% 4.84/1.94  #Fact    : 0
% 4.84/1.94  #Define  : 0
% 4.84/1.94  #Split   : 9
% 4.84/1.94  #Chain   : 0
% 4.84/1.94  #Close   : 0
% 4.84/1.94  
% 4.84/1.94  Ordering : KBO
% 4.84/1.94  
% 4.84/1.94  Simplification rules
% 4.84/1.94  ----------------------
% 4.84/1.94  #Subsume      : 85
% 4.84/1.94  #Demod        : 312
% 4.84/1.94  #Tautology    : 539
% 4.84/1.94  #SimpNegUnit  : 17
% 4.84/1.94  #BackRed      : 45
% 4.84/1.94  
% 4.84/1.94  #Partial instantiations: 59
% 4.84/1.94  #Strategies tried      : 1
% 4.84/1.94  
% 4.84/1.94  Timing (in seconds)
% 4.84/1.94  ----------------------
% 4.84/1.94  Preprocessing        : 0.36
% 4.84/1.94  Parsing              : 0.19
% 4.84/1.94  CNF conversion       : 0.03
% 4.84/1.94  Main loop            : 0.75
% 4.84/1.94  Inferencing          : 0.30
% 4.84/1.94  Reduction            : 0.24
% 4.84/1.94  Demodulation         : 0.18
% 4.84/1.94  BG Simplification    : 0.03
% 4.84/1.94  Subsumption          : 0.11
% 4.84/1.94  Abstraction          : 0.03
% 4.84/1.94  MUC search           : 0.00
% 4.84/1.94  Cooper               : 0.00
% 4.84/1.94  Total                : 1.15
% 4.84/1.94  Index Insertion      : 0.00
% 4.84/1.95  Index Deletion       : 0.00
% 4.84/1.95  Index Matching       : 0.00
% 4.84/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
