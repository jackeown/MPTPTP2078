%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:27 EST 2020

% Result     : Theorem 5.20s
% Output     : CNFRefutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 515 expanded)
%              Number of leaves         :   28 ( 181 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 978 expanded)
%              Number of equality atoms :   32 ( 254 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_26,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_6','#skF_8')
    | ~ r1_tarski('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_94,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    ! [B_33] : k3_xboole_0(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_24])).

tff(c_174,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_177,plain,(
    ! [B_33,C_41] :
      ( ~ r1_xboole_0(k1_xboole_0,B_33)
      | ~ r2_hidden(C_41,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_174])).

tff(c_183,plain,(
    ! [C_41] : ~ r2_hidden(C_41,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_238,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_4'(A_53,B_54),k3_xboole_0(A_53,B_54))
      | r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_246,plain,(
    ! [B_33] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_33),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_238])).

tff(c_249,plain,(
    ! [B_33] : r1_xboole_0(k1_xboole_0,B_33) ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_246])).

tff(c_423,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_2'(A_82,B_83),B_83)
      | r2_hidden('#skF_3'(A_82,B_83),A_82)
      | B_83 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_900,plain,(
    ! [A_127,B_128,A_129] :
      ( ~ r1_xboole_0(A_127,B_128)
      | r2_hidden('#skF_3'(A_129,k3_xboole_0(A_127,B_128)),A_129)
      | k3_xboole_0(A_127,B_128) = A_129 ) ),
    inference(resolution,[status(thm)],[c_423,c_18])).

tff(c_926,plain,(
    ! [B_33,A_129] :
      ( ~ r1_xboole_0(k1_xboole_0,B_33)
      | r2_hidden('#skF_3'(A_129,k1_xboole_0),A_129)
      | k3_xboole_0(k1_xboole_0,B_33) = A_129 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_900])).

tff(c_936,plain,(
    ! [A_129] :
      ( r2_hidden('#skF_3'(A_129,k1_xboole_0),A_129)
      | k1_xboole_0 = A_129 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_249,c_926])).

tff(c_44,plain,(
    r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_454,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( r2_hidden(k4_tarski(A_84,B_85),k2_zfmisc_1(C_86,D_87))
      | ~ r2_hidden(B_85,D_87)
      | ~ r2_hidden(A_84,C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1571,plain,(
    ! [A_195,C_194,B_196,D_198,B_197] :
      ( r2_hidden(k4_tarski(A_195,B_196),B_197)
      | ~ r1_tarski(k2_zfmisc_1(C_194,D_198),B_197)
      | ~ r2_hidden(B_196,D_198)
      | ~ r2_hidden(A_195,C_194) ) ),
    inference(resolution,[status(thm)],[c_454,c_2])).

tff(c_1602,plain,(
    ! [A_202,B_203] :
      ( r2_hidden(k4_tarski(A_202,B_203),k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(B_203,'#skF_6')
      | ~ r2_hidden(A_202,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_1571])).

tff(c_30,plain,(
    ! [B_20,D_22,A_19,C_21] :
      ( r2_hidden(B_20,D_22)
      | ~ r2_hidden(k4_tarski(A_19,B_20),k2_zfmisc_1(C_21,D_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1615,plain,(
    ! [B_203,A_202] :
      ( r2_hidden(B_203,'#skF_8')
      | ~ r2_hidden(B_203,'#skF_6')
      | ~ r2_hidden(A_202,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1602,c_30])).

tff(c_1620,plain,(
    ! [A_204] : ~ r2_hidden(A_204,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1615])).

tff(c_1716,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1620])).

tff(c_1827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_94])).

tff(c_1842,plain,(
    ! [B_210] :
      ( r2_hidden(B_210,'#skF_8')
      | ~ r2_hidden(B_210,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_1615])).

tff(c_1928,plain,
    ( r2_hidden('#skF_3'('#skF_6',k1_xboole_0),'#skF_8')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_936,c_1842])).

tff(c_1939,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1928])).

tff(c_36,plain,(
    ! [A_23] : k2_zfmisc_1(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1972,plain,(
    ! [A_23] : k2_zfmisc_1(A_23,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1939,c_1939,c_36])).

tff(c_42,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1974,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1939,c_42])).

tff(c_2296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1972,c_1974])).

tff(c_2298,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1928])).

tff(c_32,plain,(
    ! [A_19,C_21,B_20,D_22] :
      ( r2_hidden(A_19,C_21)
      | ~ r2_hidden(k4_tarski(A_19,B_20),k2_zfmisc_1(C_21,D_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1616,plain,(
    ! [A_202,B_203] :
      ( r2_hidden(A_202,'#skF_7')
      | ~ r2_hidden(B_203,'#skF_6')
      | ~ r2_hidden(A_202,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1602,c_32])).

tff(c_2551,plain,(
    ! [B_241] : ~ r2_hidden(B_241,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1616])).

tff(c_2595,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_936,c_2551])).

tff(c_2650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2298,c_2595])).

tff(c_2663,plain,(
    ! [A_242] :
      ( r2_hidden(A_242,'#skF_7')
      | ~ r2_hidden(A_242,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_1616])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2706,plain,(
    ! [A_247] :
      ( r1_tarski(A_247,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_247,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2663,c_4])).

tff(c_2714,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_2706])).

tff(c_2719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_94,c_2714])).

tff(c_2732,plain,(
    ! [B_250] : ~ r1_xboole_0(k1_xboole_0,B_250) ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_2737,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_26,c_2732])).

tff(c_2738,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2752,plain,(
    ! [A_255,B_256] : k4_xboole_0(A_255,k4_xboole_0(A_255,B_256)) = k3_xboole_0(A_255,B_256) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2762,plain,(
    ! [B_256] : k3_xboole_0(k1_xboole_0,B_256) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2752,c_24])).

tff(c_2790,plain,(
    ! [A_258,B_259,C_260] :
      ( ~ r1_xboole_0(A_258,B_259)
      | ~ r2_hidden(C_260,k3_xboole_0(A_258,B_259)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2793,plain,(
    ! [B_256,C_260] :
      ( ~ r1_xboole_0(k1_xboole_0,B_256)
      | ~ r2_hidden(C_260,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2762,c_2790])).

tff(c_2832,plain,(
    ! [C_260] : ~ r2_hidden(C_260,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2793])).

tff(c_2883,plain,(
    ! [A_274,B_275] :
      ( r2_hidden('#skF_4'(A_274,B_275),k3_xboole_0(A_274,B_275))
      | r1_xboole_0(A_274,B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2891,plain,(
    ! [B_256] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_256),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_256) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2762,c_2883])).

tff(c_2894,plain,(
    ! [B_256] : r1_xboole_0(k1_xboole_0,B_256) ),
    inference(negUnitSimplification,[status(thm)],[c_2832,c_2891])).

tff(c_3027,plain,(
    ! [A_293,B_294] :
      ( r2_hidden('#skF_2'(A_293,B_294),B_294)
      | r2_hidden('#skF_3'(A_293,B_294),A_293)
      | B_294 = A_293 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3594,plain,(
    ! [A_350,B_351,A_352] :
      ( ~ r1_xboole_0(A_350,B_351)
      | r2_hidden('#skF_3'(A_352,k3_xboole_0(A_350,B_351)),A_352)
      | k3_xboole_0(A_350,B_351) = A_352 ) ),
    inference(resolution,[status(thm)],[c_3027,c_18])).

tff(c_3620,plain,(
    ! [B_256,A_352] :
      ( ~ r1_xboole_0(k1_xboole_0,B_256)
      | r2_hidden('#skF_3'(A_352,k1_xboole_0),A_352)
      | k3_xboole_0(k1_xboole_0,B_256) = A_352 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2762,c_3594])).

tff(c_3631,plain,(
    ! [A_352] :
      ( r2_hidden('#skF_3'(A_352,k1_xboole_0),A_352)
      | k1_xboole_0 = A_352 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2762,c_2894,c_3620])).

tff(c_3274,plain,(
    ! [A_314,B_315,C_316,D_317] :
      ( r2_hidden(k4_tarski(A_314,B_315),k2_zfmisc_1(C_316,D_317))
      | ~ r2_hidden(B_315,D_317)
      | ~ r2_hidden(A_314,C_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4489,plain,(
    ! [B_451,A_448,B_447,D_450,C_449] :
      ( r2_hidden(k4_tarski(A_448,B_447),B_451)
      | ~ r1_tarski(k2_zfmisc_1(C_449,D_450),B_451)
      | ~ r2_hidden(B_447,D_450)
      | ~ r2_hidden(A_448,C_449) ) ),
    inference(resolution,[status(thm)],[c_3274,c_2])).

tff(c_4538,plain,(
    ! [A_455,B_456] :
      ( r2_hidden(k4_tarski(A_455,B_456),k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(B_456,'#skF_6')
      | ~ r2_hidden(A_455,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_4489])).

tff(c_4552,plain,(
    ! [B_456,A_455] :
      ( r2_hidden(B_456,'#skF_8')
      | ~ r2_hidden(B_456,'#skF_6')
      | ~ r2_hidden(A_455,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4538,c_30])).

tff(c_4817,plain,(
    ! [A_468] : ~ r2_hidden(A_468,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4552])).

tff(c_4913,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3631,c_4817])).

tff(c_38,plain,(
    ! [B_24] : k2_zfmisc_1(k1_xboole_0,B_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4967,plain,(
    ! [B_24] : k2_zfmisc_1('#skF_5',B_24) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4913,c_4913,c_38])).

tff(c_4968,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4913,c_42])).

tff(c_5227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4967,c_4968])).

tff(c_5229,plain,(
    ! [B_481] :
      ( r2_hidden(B_481,'#skF_8')
      | ~ r2_hidden(B_481,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_4552])).

tff(c_5631,plain,(
    ! [B_491] :
      ( r2_hidden('#skF_1'('#skF_6',B_491),'#skF_8')
      | r1_tarski('#skF_6',B_491) ) ),
    inference(resolution,[status(thm)],[c_6,c_5229])).

tff(c_5640,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_5631,c_4])).

tff(c_5646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2738,c_2738,c_5640])).

tff(c_5648,plain,(
    ! [B_492] : ~ r1_xboole_0(k1_xboole_0,B_492) ),
    inference(splitRight,[status(thm)],[c_2793])).

tff(c_5653,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_26,c_5648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.20/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/2.05  
% 5.20/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/2.05  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 5.20/2.05  
% 5.20/2.05  %Foreground sorts:
% 5.20/2.05  
% 5.20/2.05  
% 5.20/2.05  %Background operators:
% 5.20/2.05  
% 5.20/2.05  
% 5.20/2.05  %Foreground operators:
% 5.20/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.20/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.20/2.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.20/2.05  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.20/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.20/2.05  tff('#skF_7', type, '#skF_7': $i).
% 5.20/2.05  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.20/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.20/2.05  tff('#skF_5', type, '#skF_5': $i).
% 5.20/2.05  tff('#skF_6', type, '#skF_6': $i).
% 5.20/2.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.20/2.05  tff('#skF_8', type, '#skF_8': $i).
% 5.20/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.20/2.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.20/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.20/2.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.20/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.20/2.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.20/2.05  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.20/2.05  
% 5.55/2.07  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.55/2.07  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 5.55/2.07  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.55/2.07  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.55/2.07  tff(f_59, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 5.55/2.07  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.55/2.07  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 5.55/2.07  tff(f_67, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.55/2.07  tff(f_73, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.55/2.07  tff(c_26, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.55/2.07  tff(c_40, plain, (~r1_tarski('#skF_6', '#skF_8') | ~r1_tarski('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.55/2.07  tff(c_94, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_40])).
% 5.55/2.07  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.55/2.07  tff(c_96, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.55/2.07  tff(c_24, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.55/2.07  tff(c_106, plain, (![B_33]: (k3_xboole_0(k1_xboole_0, B_33)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96, c_24])).
% 5.55/2.07  tff(c_174, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.55/2.07  tff(c_177, plain, (![B_33, C_41]: (~r1_xboole_0(k1_xboole_0, B_33) | ~r2_hidden(C_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_106, c_174])).
% 5.55/2.07  tff(c_183, plain, (![C_41]: (~r2_hidden(C_41, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_177])).
% 5.55/2.07  tff(c_238, plain, (![A_53, B_54]: (r2_hidden('#skF_4'(A_53, B_54), k3_xboole_0(A_53, B_54)) | r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.55/2.07  tff(c_246, plain, (![B_33]: (r2_hidden('#skF_4'(k1_xboole_0, B_33), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_33))), inference(superposition, [status(thm), theory('equality')], [c_106, c_238])).
% 5.55/2.07  tff(c_249, plain, (![B_33]: (r1_xboole_0(k1_xboole_0, B_33))), inference(negUnitSimplification, [status(thm)], [c_183, c_246])).
% 5.55/2.07  tff(c_423, plain, (![A_82, B_83]: (r2_hidden('#skF_2'(A_82, B_83), B_83) | r2_hidden('#skF_3'(A_82, B_83), A_82) | B_83=A_82)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.55/2.07  tff(c_18, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.55/2.07  tff(c_900, plain, (![A_127, B_128, A_129]: (~r1_xboole_0(A_127, B_128) | r2_hidden('#skF_3'(A_129, k3_xboole_0(A_127, B_128)), A_129) | k3_xboole_0(A_127, B_128)=A_129)), inference(resolution, [status(thm)], [c_423, c_18])).
% 5.55/2.07  tff(c_926, plain, (![B_33, A_129]: (~r1_xboole_0(k1_xboole_0, B_33) | r2_hidden('#skF_3'(A_129, k1_xboole_0), A_129) | k3_xboole_0(k1_xboole_0, B_33)=A_129)), inference(superposition, [status(thm), theory('equality')], [c_106, c_900])).
% 5.55/2.07  tff(c_936, plain, (![A_129]: (r2_hidden('#skF_3'(A_129, k1_xboole_0), A_129) | k1_xboole_0=A_129)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_249, c_926])).
% 5.55/2.07  tff(c_44, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.55/2.07  tff(c_454, plain, (![A_84, B_85, C_86, D_87]: (r2_hidden(k4_tarski(A_84, B_85), k2_zfmisc_1(C_86, D_87)) | ~r2_hidden(B_85, D_87) | ~r2_hidden(A_84, C_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.55/2.07  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.55/2.07  tff(c_1571, plain, (![A_195, C_194, B_196, D_198, B_197]: (r2_hidden(k4_tarski(A_195, B_196), B_197) | ~r1_tarski(k2_zfmisc_1(C_194, D_198), B_197) | ~r2_hidden(B_196, D_198) | ~r2_hidden(A_195, C_194))), inference(resolution, [status(thm)], [c_454, c_2])).
% 5.55/2.07  tff(c_1602, plain, (![A_202, B_203]: (r2_hidden(k4_tarski(A_202, B_203), k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(B_203, '#skF_6') | ~r2_hidden(A_202, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_1571])).
% 5.55/2.07  tff(c_30, plain, (![B_20, D_22, A_19, C_21]: (r2_hidden(B_20, D_22) | ~r2_hidden(k4_tarski(A_19, B_20), k2_zfmisc_1(C_21, D_22)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.55/2.07  tff(c_1615, plain, (![B_203, A_202]: (r2_hidden(B_203, '#skF_8') | ~r2_hidden(B_203, '#skF_6') | ~r2_hidden(A_202, '#skF_5'))), inference(resolution, [status(thm)], [c_1602, c_30])).
% 5.55/2.07  tff(c_1620, plain, (![A_204]: (~r2_hidden(A_204, '#skF_5'))), inference(splitLeft, [status(thm)], [c_1615])).
% 5.55/2.07  tff(c_1716, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_1620])).
% 5.55/2.07  tff(c_1827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1716, c_94])).
% 5.55/2.07  tff(c_1842, plain, (![B_210]: (r2_hidden(B_210, '#skF_8') | ~r2_hidden(B_210, '#skF_6'))), inference(splitRight, [status(thm)], [c_1615])).
% 5.55/2.07  tff(c_1928, plain, (r2_hidden('#skF_3'('#skF_6', k1_xboole_0), '#skF_8') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_936, c_1842])).
% 5.55/2.07  tff(c_1939, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_1928])).
% 5.55/2.07  tff(c_36, plain, (![A_23]: (k2_zfmisc_1(A_23, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.55/2.07  tff(c_1972, plain, (![A_23]: (k2_zfmisc_1(A_23, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1939, c_1939, c_36])).
% 5.55/2.07  tff(c_42, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.55/2.07  tff(c_1974, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1939, c_42])).
% 5.55/2.07  tff(c_2296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1972, c_1974])).
% 5.55/2.07  tff(c_2298, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_1928])).
% 5.55/2.07  tff(c_32, plain, (![A_19, C_21, B_20, D_22]: (r2_hidden(A_19, C_21) | ~r2_hidden(k4_tarski(A_19, B_20), k2_zfmisc_1(C_21, D_22)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.55/2.07  tff(c_1616, plain, (![A_202, B_203]: (r2_hidden(A_202, '#skF_7') | ~r2_hidden(B_203, '#skF_6') | ~r2_hidden(A_202, '#skF_5'))), inference(resolution, [status(thm)], [c_1602, c_32])).
% 5.55/2.07  tff(c_2551, plain, (![B_241]: (~r2_hidden(B_241, '#skF_6'))), inference(splitLeft, [status(thm)], [c_1616])).
% 5.55/2.07  tff(c_2595, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_936, c_2551])).
% 5.55/2.07  tff(c_2650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2298, c_2595])).
% 5.55/2.07  tff(c_2663, plain, (![A_242]: (r2_hidden(A_242, '#skF_7') | ~r2_hidden(A_242, '#skF_5'))), inference(splitRight, [status(thm)], [c_1616])).
% 5.55/2.07  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.55/2.07  tff(c_2706, plain, (![A_247]: (r1_tarski(A_247, '#skF_7') | ~r2_hidden('#skF_1'(A_247, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_2663, c_4])).
% 5.55/2.07  tff(c_2714, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_2706])).
% 5.55/2.07  tff(c_2719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_94, c_2714])).
% 5.55/2.07  tff(c_2732, plain, (![B_250]: (~r1_xboole_0(k1_xboole_0, B_250))), inference(splitRight, [status(thm)], [c_177])).
% 5.55/2.07  tff(c_2737, plain, $false, inference(resolution, [status(thm)], [c_26, c_2732])).
% 5.55/2.07  tff(c_2738, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_40])).
% 5.55/2.07  tff(c_2752, plain, (![A_255, B_256]: (k4_xboole_0(A_255, k4_xboole_0(A_255, B_256))=k3_xboole_0(A_255, B_256))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.55/2.07  tff(c_2762, plain, (![B_256]: (k3_xboole_0(k1_xboole_0, B_256)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2752, c_24])).
% 5.55/2.07  tff(c_2790, plain, (![A_258, B_259, C_260]: (~r1_xboole_0(A_258, B_259) | ~r2_hidden(C_260, k3_xboole_0(A_258, B_259)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.55/2.07  tff(c_2793, plain, (![B_256, C_260]: (~r1_xboole_0(k1_xboole_0, B_256) | ~r2_hidden(C_260, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2762, c_2790])).
% 5.55/2.07  tff(c_2832, plain, (![C_260]: (~r2_hidden(C_260, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2793])).
% 5.55/2.07  tff(c_2883, plain, (![A_274, B_275]: (r2_hidden('#skF_4'(A_274, B_275), k3_xboole_0(A_274, B_275)) | r1_xboole_0(A_274, B_275))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.55/2.07  tff(c_2891, plain, (![B_256]: (r2_hidden('#skF_4'(k1_xboole_0, B_256), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_256))), inference(superposition, [status(thm), theory('equality')], [c_2762, c_2883])).
% 5.55/2.07  tff(c_2894, plain, (![B_256]: (r1_xboole_0(k1_xboole_0, B_256))), inference(negUnitSimplification, [status(thm)], [c_2832, c_2891])).
% 5.55/2.07  tff(c_3027, plain, (![A_293, B_294]: (r2_hidden('#skF_2'(A_293, B_294), B_294) | r2_hidden('#skF_3'(A_293, B_294), A_293) | B_294=A_293)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.55/2.07  tff(c_3594, plain, (![A_350, B_351, A_352]: (~r1_xboole_0(A_350, B_351) | r2_hidden('#skF_3'(A_352, k3_xboole_0(A_350, B_351)), A_352) | k3_xboole_0(A_350, B_351)=A_352)), inference(resolution, [status(thm)], [c_3027, c_18])).
% 5.55/2.07  tff(c_3620, plain, (![B_256, A_352]: (~r1_xboole_0(k1_xboole_0, B_256) | r2_hidden('#skF_3'(A_352, k1_xboole_0), A_352) | k3_xboole_0(k1_xboole_0, B_256)=A_352)), inference(superposition, [status(thm), theory('equality')], [c_2762, c_3594])).
% 5.55/2.07  tff(c_3631, plain, (![A_352]: (r2_hidden('#skF_3'(A_352, k1_xboole_0), A_352) | k1_xboole_0=A_352)), inference(demodulation, [status(thm), theory('equality')], [c_2762, c_2894, c_3620])).
% 5.55/2.07  tff(c_3274, plain, (![A_314, B_315, C_316, D_317]: (r2_hidden(k4_tarski(A_314, B_315), k2_zfmisc_1(C_316, D_317)) | ~r2_hidden(B_315, D_317) | ~r2_hidden(A_314, C_316))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.55/2.07  tff(c_4489, plain, (![B_451, A_448, B_447, D_450, C_449]: (r2_hidden(k4_tarski(A_448, B_447), B_451) | ~r1_tarski(k2_zfmisc_1(C_449, D_450), B_451) | ~r2_hidden(B_447, D_450) | ~r2_hidden(A_448, C_449))), inference(resolution, [status(thm)], [c_3274, c_2])).
% 5.55/2.07  tff(c_4538, plain, (![A_455, B_456]: (r2_hidden(k4_tarski(A_455, B_456), k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(B_456, '#skF_6') | ~r2_hidden(A_455, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_4489])).
% 5.55/2.07  tff(c_4552, plain, (![B_456, A_455]: (r2_hidden(B_456, '#skF_8') | ~r2_hidden(B_456, '#skF_6') | ~r2_hidden(A_455, '#skF_5'))), inference(resolution, [status(thm)], [c_4538, c_30])).
% 5.55/2.07  tff(c_4817, plain, (![A_468]: (~r2_hidden(A_468, '#skF_5'))), inference(splitLeft, [status(thm)], [c_4552])).
% 5.55/2.07  tff(c_4913, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3631, c_4817])).
% 5.55/2.07  tff(c_38, plain, (![B_24]: (k2_zfmisc_1(k1_xboole_0, B_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.55/2.07  tff(c_4967, plain, (![B_24]: (k2_zfmisc_1('#skF_5', B_24)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4913, c_4913, c_38])).
% 5.55/2.07  tff(c_4968, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4913, c_42])).
% 5.55/2.07  tff(c_5227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4967, c_4968])).
% 5.55/2.07  tff(c_5229, plain, (![B_481]: (r2_hidden(B_481, '#skF_8') | ~r2_hidden(B_481, '#skF_6'))), inference(splitRight, [status(thm)], [c_4552])).
% 5.55/2.07  tff(c_5631, plain, (![B_491]: (r2_hidden('#skF_1'('#skF_6', B_491), '#skF_8') | r1_tarski('#skF_6', B_491))), inference(resolution, [status(thm)], [c_6, c_5229])).
% 5.55/2.07  tff(c_5640, plain, (r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_5631, c_4])).
% 5.55/2.07  tff(c_5646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2738, c_2738, c_5640])).
% 5.55/2.07  tff(c_5648, plain, (![B_492]: (~r1_xboole_0(k1_xboole_0, B_492))), inference(splitRight, [status(thm)], [c_2793])).
% 5.55/2.07  tff(c_5653, plain, $false, inference(resolution, [status(thm)], [c_26, c_5648])).
% 5.55/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.07  
% 5.55/2.07  Inference rules
% 5.55/2.07  ----------------------
% 5.55/2.07  #Ref     : 0
% 5.55/2.07  #Sup     : 1181
% 5.55/2.07  #Fact    : 0
% 5.55/2.07  #Define  : 0
% 5.55/2.07  #Split   : 15
% 5.55/2.07  #Chain   : 0
% 5.55/2.07  #Close   : 0
% 5.55/2.07  
% 5.55/2.07  Ordering : KBO
% 5.55/2.07  
% 5.55/2.07  Simplification rules
% 5.55/2.07  ----------------------
% 5.55/2.07  #Subsume      : 390
% 5.55/2.07  #Demod        : 698
% 5.55/2.07  #Tautology    : 305
% 5.55/2.07  #SimpNegUnit  : 31
% 5.55/2.07  #BackRed      : 225
% 5.55/2.07  
% 5.55/2.07  #Partial instantiations: 0
% 5.55/2.07  #Strategies tried      : 1
% 5.55/2.07  
% 5.55/2.07  Timing (in seconds)
% 5.55/2.07  ----------------------
% 5.55/2.07  Preprocessing        : 0.29
% 5.55/2.07  Parsing              : 0.16
% 5.55/2.07  CNF conversion       : 0.02
% 5.55/2.07  Main loop            : 0.99
% 5.55/2.07  Inferencing          : 0.36
% 5.55/2.07  Reduction            : 0.30
% 5.55/2.07  Demodulation         : 0.20
% 5.55/2.07  BG Simplification    : 0.03
% 5.55/2.07  Subsumption          : 0.21
% 5.55/2.07  Abstraction          : 0.04
% 5.55/2.07  MUC search           : 0.00
% 5.55/2.07  Cooper               : 0.00
% 5.55/2.07  Total                : 1.32
% 5.55/2.07  Index Insertion      : 0.00
% 5.55/2.07  Index Deletion       : 0.00
% 5.55/2.07  Index Matching       : 0.00
% 5.55/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
