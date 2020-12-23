%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:32 EST 2020

% Result     : Theorem 9.03s
% Output     : CNFRefutation 9.52s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 321 expanded)
%              Number of leaves         :   35 ( 115 expanded)
%              Depth                    :   13
%              Number of atoms          :  241 ( 655 expanded)
%              Number of equality atoms :   27 ( 149 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
      <=> ( r2_hidden(A,B)
          & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_36,plain,(
    ! [C_26] : r2_hidden(C_26,k1_tarski(C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_81,plain,(
    ! [B_54,A_55] : k3_xboole_0(B_54,A_55) = k3_xboole_0(A_55,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_96,plain,(
    ! [B_54,A_55] : r1_tarski(k3_xboole_0(B_54,A_55),A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_30])).

tff(c_66,plain,
    ( '#skF_7' != '#skF_5'
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_186,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_68,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_187,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_2'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_249,plain,(
    ! [C_84,B_85,A_86] :
      ( r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_263,plain,(
    ! [A_11,B_12,B_85] :
      ( r2_hidden('#skF_2'(A_11,B_12),B_85)
      | ~ r1_tarski(A_11,B_85)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_26,c_249])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_2'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_225,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,B_79)
      | ~ r2_hidden(C_80,A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_229,plain,(
    ! [C_81,B_82,A_83] :
      ( ~ r2_hidden(C_81,B_82)
      | ~ r2_hidden(C_81,k4_xboole_0(A_83,B_82)) ) ),
    inference(resolution,[status(thm)],[c_32,c_225])).

tff(c_1489,plain,(
    ! [A_2604,A_2605,B_2606] :
      ( ~ r2_hidden('#skF_2'(A_2604,k4_xboole_0(A_2605,B_2606)),B_2606)
      | r1_xboole_0(A_2604,k4_xboole_0(A_2605,B_2606)) ) ),
    inference(resolution,[status(thm)],[c_24,c_229])).

tff(c_1553,plain,(
    ! [A_2735,B_2736,A_2737] :
      ( ~ r1_tarski(A_2735,B_2736)
      | r1_xboole_0(A_2735,k4_xboole_0(A_2737,B_2736)) ) ),
    inference(resolution,[status(thm)],[c_263,c_1489])).

tff(c_22,plain,(
    ! [A_11,B_12,C_15] :
      ( ~ r1_xboole_0(A_11,B_12)
      | ~ r2_hidden(C_15,B_12)
      | ~ r2_hidden(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1601,plain,(
    ! [C_2870,A_2871,B_2872,A_2873] :
      ( ~ r2_hidden(C_2870,k4_xboole_0(A_2871,B_2872))
      | ~ r2_hidden(C_2870,A_2873)
      | ~ r1_tarski(A_2873,B_2872) ) ),
    inference(resolution,[status(thm)],[c_1553,c_22])).

tff(c_1644,plain,(
    ! [A_2963] :
      ( ~ r2_hidden('#skF_8',A_2963)
      | ~ r1_tarski(A_2963,k1_tarski('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_187,c_1601])).

tff(c_1667,plain,(
    ! [B_54] : ~ r2_hidden('#skF_8',k3_xboole_0(B_54,k1_tarski('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_96,c_1644])).

tff(c_60,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_145,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_28,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_378,plain,(
    ! [A_111,B_112,C_113] :
      ( r2_hidden(A_111,B_112)
      | r2_hidden(A_111,C_113)
      | ~ r2_hidden(A_111,k5_xboole_0(B_112,C_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2963,plain,(
    ! [A_4070,A_4071,B_4072] :
      ( r2_hidden(A_4070,A_4071)
      | r2_hidden(A_4070,k3_xboole_0(A_4071,B_4072))
      | ~ r2_hidden(A_4070,k4_xboole_0(A_4071,B_4072)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_378])).

tff(c_2989,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_187,c_2963])).

tff(c_3011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1667,c_145,c_2989])).

tff(c_3012,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_3781,plain,(
    ! [A_5837,C_5838,B_5839] :
      ( r2_hidden(A_5837,C_5838)
      | ~ r2_hidden(A_5837,B_5839)
      | r2_hidden(A_5837,k5_xboole_0(B_5839,C_5838)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5322,plain,(
    ! [A_8275,A_8276,B_8277] :
      ( r2_hidden(A_8275,k3_xboole_0(A_8276,B_8277))
      | ~ r2_hidden(A_8275,A_8276)
      | r2_hidden(A_8275,k4_xboole_0(A_8276,B_8277)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3781])).

tff(c_3013,plain,(
    ~ r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3092,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3013,c_64])).

tff(c_5370,plain,
    ( r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_5322,c_3092])).

tff(c_5398,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3012,c_5370])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5464,plain,(
    ! [B_8362] :
      ( r2_hidden('#skF_5',B_8362)
      | ~ r1_tarski(k3_xboole_0('#skF_6',k1_tarski('#skF_7')),B_8362) ) ),
    inference(resolution,[status(thm)],[c_5398,c_4])).

tff(c_5484,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_96,c_5464])).

tff(c_34,plain,(
    ! [C_26,A_22] :
      ( C_26 = A_22
      | ~ r2_hidden(C_26,k1_tarski(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5502,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5484,c_34])).

tff(c_5562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_5502])).

tff(c_5563,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5608,plain,(
    ! [C_8452,B_8453,A_8454] :
      ( r2_hidden(C_8452,B_8453)
      | ~ r2_hidden(C_8452,A_8454)
      | ~ r1_tarski(A_8454,B_8453) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5622,plain,(
    ! [A_11,B_12,B_8453] :
      ( r2_hidden('#skF_2'(A_11,B_12),B_8453)
      | ~ r1_tarski(A_11,B_8453)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_26,c_5608])).

tff(c_5631,plain,(
    ! [A_8457,B_8458,C_8459] :
      ( ~ r1_xboole_0(A_8457,B_8458)
      | ~ r2_hidden(C_8459,B_8458)
      | ~ r2_hidden(C_8459,A_8457) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5636,plain,(
    ! [C_8460,B_8461,A_8462] :
      ( ~ r2_hidden(C_8460,B_8461)
      | ~ r2_hidden(C_8460,k4_xboole_0(A_8462,B_8461)) ) ),
    inference(resolution,[status(thm)],[c_32,c_5631])).

tff(c_7105,plain,(
    ! [A_10965,A_10966,B_10967] :
      ( ~ r2_hidden('#skF_2'(A_10965,k4_xboole_0(A_10966,B_10967)),B_10967)
      | r1_xboole_0(A_10965,k4_xboole_0(A_10966,B_10967)) ) ),
    inference(resolution,[status(thm)],[c_24,c_5636])).

tff(c_7166,plain,(
    ! [A_11054,B_11055,A_11056] :
      ( ~ r1_tarski(A_11054,B_11055)
      | r1_xboole_0(A_11054,k4_xboole_0(A_11056,B_11055)) ) ),
    inference(resolution,[status(thm)],[c_5622,c_7105])).

tff(c_7274,plain,(
    ! [C_11233,A_11234,B_11235,A_11236] :
      ( ~ r2_hidden(C_11233,k4_xboole_0(A_11234,B_11235))
      | ~ r2_hidden(C_11233,A_11236)
      | ~ r1_tarski(A_11236,B_11235) ) ),
    inference(resolution,[status(thm)],[c_7166,c_22])).

tff(c_7307,plain,(
    ! [A_11279] :
      ( ~ r2_hidden('#skF_8',A_11279)
      | ~ r1_tarski(A_11279,k1_tarski('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_5563,c_7274])).

tff(c_7330,plain,(
    ! [B_54] : ~ r2_hidden('#skF_8',k3_xboole_0(B_54,k1_tarski('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_96,c_7307])).

tff(c_5734,plain,(
    ! [A_8478,B_8479,C_8480] :
      ( r2_hidden(A_8478,B_8479)
      | r2_hidden(A_8478,C_8480)
      | ~ r2_hidden(A_8478,k5_xboole_0(B_8479,C_8480)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8006,plain,(
    ! [A_12162,A_12163,B_12164] :
      ( r2_hidden(A_12162,A_12163)
      | r2_hidden(A_12162,k3_xboole_0(A_12163,B_12164))
      | ~ r2_hidden(A_12162,k4_xboole_0(A_12163,B_12164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_5734])).

tff(c_8029,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_5563,c_8006])).

tff(c_8050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7330,c_145,c_8029])).

tff(c_8051,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_8053,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_8051])).

tff(c_8052,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8055,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8052,c_62])).

tff(c_8056,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_8055])).

tff(c_8129,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8056,c_68])).

tff(c_8130,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_8129])).

tff(c_8141,plain,(
    ! [A_12223,B_12224,C_12225] :
      ( ~ r1_xboole_0(A_12223,B_12224)
      | ~ r2_hidden(C_12225,B_12224)
      | ~ r2_hidden(C_12225,A_12223) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8145,plain,(
    ! [C_12226,B_12227,A_12228] :
      ( ~ r2_hidden(C_12226,B_12227)
      | ~ r2_hidden(C_12226,k4_xboole_0(A_12228,B_12227)) ) ),
    inference(resolution,[status(thm)],[c_32,c_8141])).

tff(c_8148,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_8130,c_8145])).

tff(c_8164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8148])).

tff(c_8165,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_8129])).

tff(c_9031,plain,(
    ! [A_14430,C_14431,B_14432] :
      ( r2_hidden(A_14430,C_14431)
      | ~ r2_hidden(A_14430,B_14432)
      | r2_hidden(A_14430,k5_xboole_0(B_14432,C_14431)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11083,plain,(
    ! [A_17708,A_17709,B_17710] :
      ( r2_hidden(A_17708,k3_xboole_0(A_17709,B_17710))
      | ~ r2_hidden(A_17708,A_17709)
      | r2_hidden(A_17708,k4_xboole_0(A_17709,B_17710)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_9031])).

tff(c_8166,plain,(
    ~ r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_8129])).

tff(c_8284,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8056,c_64])).

tff(c_8285,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_8166,c_8284])).

tff(c_11139,plain,
    ( r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_11083,c_8285])).

tff(c_11172,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8165,c_11139])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_9007,plain,(
    ! [A_14385,B_14386,C_14387] :
      ( r2_hidden(A_14385,B_14386)
      | ~ r2_hidden(A_14385,C_14387)
      | r2_hidden(A_14385,k5_xboole_0(B_14386,C_14387)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10453,plain,(
    ! [A_16949,A_16950,B_16951] :
      ( r2_hidden(A_16949,A_16950)
      | ~ r2_hidden(A_16949,k3_xboole_0(A_16950,B_16951))
      | r2_hidden(A_16949,k4_xboole_0(A_16950,B_16951)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_9007])).

tff(c_8179,plain,(
    ! [A_12232,B_12233,C_12234] :
      ( ~ r1_xboole_0(A_12232,B_12233)
      | ~ r2_hidden(C_12234,B_12233)
      | ~ r2_hidden(C_12234,A_12232) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8182,plain,(
    ! [C_12234,B_21,A_20] :
      ( ~ r2_hidden(C_12234,B_21)
      | ~ r2_hidden(C_12234,k4_xboole_0(A_20,B_21)) ) ),
    inference(resolution,[status(thm)],[c_32,c_8179])).

tff(c_10535,plain,(
    ! [A_16994,B_16995,A_16996] :
      ( ~ r2_hidden(A_16994,B_16995)
      | r2_hidden(A_16994,A_16996)
      | ~ r2_hidden(A_16994,k3_xboole_0(A_16996,B_16995)) ) ),
    inference(resolution,[status(thm)],[c_10453,c_8182])).

tff(c_10575,plain,(
    ! [A_16994,B_2,A_1] :
      ( ~ r2_hidden(A_16994,B_2)
      | r2_hidden(A_16994,A_1)
      | ~ r2_hidden(A_16994,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10535])).

tff(c_11271,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_11172,c_10575])).

tff(c_11339,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8165,c_11271])).

tff(c_11361,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_11339,c_34])).

tff(c_11420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8053,c_11361])).

tff(c_11421,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_8055])).

tff(c_11736,plain,(
    ! [A_17946,C_17947,B_17948] :
      ( r2_hidden(A_17946,C_17947)
      | ~ r2_hidden(A_17946,B_17948)
      | r2_hidden(A_17946,k5_xboole_0(B_17948,C_17947)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14825,plain,(
    ! [A_23763,A_23764,B_23765] :
      ( r2_hidden(A_23763,k3_xboole_0(A_23764,B_23765))
      | ~ r2_hidden(A_23763,A_23764)
      | r2_hidden(A_23763,k4_xboole_0(A_23764,B_23765)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_11736])).

tff(c_11422,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_8055])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_11569,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8052,c_58])).

tff(c_11570,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_11422,c_11569])).

tff(c_14873,plain,
    ( r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_14825,c_11570])).

tff(c_14899,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11421,c_14873])).

tff(c_11717,plain,(
    ! [A_17943,B_17944,C_17945] :
      ( r2_hidden(A_17943,B_17944)
      | ~ r2_hidden(A_17943,C_17945)
      | r2_hidden(A_17943,k5_xboole_0(B_17944,C_17945)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13743,plain,(
    ! [A_22221,A_22222,B_22223] :
      ( r2_hidden(A_22221,A_22222)
      | ~ r2_hidden(A_22221,k3_xboole_0(A_22222,B_22223))
      | r2_hidden(A_22221,k4_xboole_0(A_22222,B_22223)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_11717])).

tff(c_11530,plain,(
    ! [A_17898,B_17899,C_17900] :
      ( ~ r1_xboole_0(A_17898,B_17899)
      | ~ r2_hidden(C_17900,B_17899)
      | ~ r2_hidden(C_17900,A_17898) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_11542,plain,(
    ! [C_17904,B_17905,A_17906] :
      ( ~ r2_hidden(C_17904,B_17905)
      | ~ r2_hidden(C_17904,k4_xboole_0(A_17906,B_17905)) ) ),
    inference(resolution,[status(thm)],[c_32,c_11530])).

tff(c_13449,plain,(
    ! [A_21460,A_21461,B_21462] :
      ( ~ r2_hidden('#skF_2'(A_21460,k4_xboole_0(A_21461,B_21462)),B_21462)
      | r1_xboole_0(A_21460,k4_xboole_0(A_21461,B_21462)) ) ),
    inference(resolution,[status(thm)],[c_24,c_11542])).

tff(c_13531,plain,(
    ! [A_21549,A_21550] : r1_xboole_0(A_21549,k4_xboole_0(A_21550,A_21549)) ),
    inference(resolution,[status(thm)],[c_26,c_13449])).

tff(c_13535,plain,(
    ! [C_15,A_21550,A_21549] :
      ( ~ r2_hidden(C_15,k4_xboole_0(A_21550,A_21549))
      | ~ r2_hidden(C_15,A_21549) ) ),
    inference(resolution,[status(thm)],[c_13531,c_22])).

tff(c_13798,plain,(
    ! [A_22266,B_22267,A_22268] :
      ( ~ r2_hidden(A_22266,B_22267)
      | r2_hidden(A_22266,A_22268)
      | ~ r2_hidden(A_22266,k3_xboole_0(A_22268,B_22267)) ) ),
    inference(resolution,[status(thm)],[c_13743,c_13535])).

tff(c_13841,plain,(
    ! [A_22266,A_1,B_2] :
      ( ~ r2_hidden(A_22266,A_1)
      | r2_hidden(A_22266,B_2)
      | ~ r2_hidden(A_22266,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13798])).

tff(c_14906,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_14899,c_13841])).

tff(c_14970,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11421,c_14906])).

tff(c_14995,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14970,c_34])).

tff(c_15056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8053,c_14995])).

tff(c_15057,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_8051])).

tff(c_15058,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8051])).

tff(c_15072,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15057,c_15058,c_66])).

tff(c_15170,plain,(
    ! [A_23953,B_23954,C_23955] :
      ( ~ r1_xboole_0(A_23953,B_23954)
      | ~ r2_hidden(C_23955,B_23954)
      | ~ r2_hidden(C_23955,A_23953) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_15193,plain,(
    ! [C_23960,B_23961,A_23962] :
      ( ~ r2_hidden(C_23960,B_23961)
      | ~ r2_hidden(C_23960,k4_xboole_0(A_23962,B_23961)) ) ),
    inference(resolution,[status(thm)],[c_32,c_15170])).

tff(c_15212,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_15072,c_15193])).

tff(c_15220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_15212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:17:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.03/3.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.38/3.07  
% 9.38/3.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.38/3.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 9.38/3.07  
% 9.38/3.07  %Foreground sorts:
% 9.38/3.07  
% 9.38/3.07  
% 9.38/3.07  %Background operators:
% 9.38/3.07  
% 9.38/3.07  
% 9.38/3.07  %Foreground operators:
% 9.38/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.38/3.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.38/3.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.38/3.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.38/3.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.38/3.07  tff('#skF_7', type, '#skF_7': $i).
% 9.38/3.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.38/3.07  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.38/3.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.38/3.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.38/3.07  tff('#skF_10', type, '#skF_10': $i).
% 9.38/3.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.38/3.07  tff('#skF_5', type, '#skF_5': $i).
% 9.38/3.07  tff('#skF_6', type, '#skF_6': $i).
% 9.38/3.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.38/3.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.38/3.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.38/3.07  tff('#skF_9', type, '#skF_9': $i).
% 9.38/3.07  tff('#skF_8', type, '#skF_8': $i).
% 9.38/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.38/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.38/3.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.38/3.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.38/3.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.38/3.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.38/3.07  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.38/3.07  
% 9.52/3.10  tff(f_72, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.52/3.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.52/3.10  tff(f_63, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.52/3.10  tff(f_92, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 9.52/3.10  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.52/3.10  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.52/3.10  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.52/3.10  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.52/3.10  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 9.52/3.10  tff(c_36, plain, (![C_26]: (r2_hidden(C_26, k1_tarski(C_26)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.52/3.10  tff(c_81, plain, (![B_54, A_55]: (k3_xboole_0(B_54, A_55)=k3_xboole_0(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.52/3.10  tff(c_30, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.52/3.10  tff(c_96, plain, (![B_54, A_55]: (r1_tarski(k3_xboole_0(B_54, A_55), A_55))), inference(superposition, [status(thm), theory('equality')], [c_81, c_30])).
% 9.52/3.10  tff(c_66, plain, ('#skF_7'!='#skF_5' | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.52/3.10  tff(c_186, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_66])).
% 9.52/3.10  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.52/3.10  tff(c_187, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_68])).
% 9.52/3.10  tff(c_26, plain, (![A_11, B_12]: (r2_hidden('#skF_2'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.52/3.10  tff(c_249, plain, (![C_84, B_85, A_86]: (r2_hidden(C_84, B_85) | ~r2_hidden(C_84, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.52/3.10  tff(c_263, plain, (![A_11, B_12, B_85]: (r2_hidden('#skF_2'(A_11, B_12), B_85) | ~r1_tarski(A_11, B_85) | r1_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_26, c_249])).
% 9.52/3.10  tff(c_24, plain, (![A_11, B_12]: (r2_hidden('#skF_2'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.52/3.10  tff(c_32, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.52/3.10  tff(c_225, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, B_79) | ~r2_hidden(C_80, A_78))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.52/3.10  tff(c_229, plain, (![C_81, B_82, A_83]: (~r2_hidden(C_81, B_82) | ~r2_hidden(C_81, k4_xboole_0(A_83, B_82)))), inference(resolution, [status(thm)], [c_32, c_225])).
% 9.52/3.10  tff(c_1489, plain, (![A_2604, A_2605, B_2606]: (~r2_hidden('#skF_2'(A_2604, k4_xboole_0(A_2605, B_2606)), B_2606) | r1_xboole_0(A_2604, k4_xboole_0(A_2605, B_2606)))), inference(resolution, [status(thm)], [c_24, c_229])).
% 9.52/3.10  tff(c_1553, plain, (![A_2735, B_2736, A_2737]: (~r1_tarski(A_2735, B_2736) | r1_xboole_0(A_2735, k4_xboole_0(A_2737, B_2736)))), inference(resolution, [status(thm)], [c_263, c_1489])).
% 9.52/3.10  tff(c_22, plain, (![A_11, B_12, C_15]: (~r1_xboole_0(A_11, B_12) | ~r2_hidden(C_15, B_12) | ~r2_hidden(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.52/3.10  tff(c_1601, plain, (![C_2870, A_2871, B_2872, A_2873]: (~r2_hidden(C_2870, k4_xboole_0(A_2871, B_2872)) | ~r2_hidden(C_2870, A_2873) | ~r1_tarski(A_2873, B_2872))), inference(resolution, [status(thm)], [c_1553, c_22])).
% 9.52/3.10  tff(c_1644, plain, (![A_2963]: (~r2_hidden('#skF_8', A_2963) | ~r1_tarski(A_2963, k1_tarski('#skF_10')))), inference(resolution, [status(thm)], [c_187, c_1601])).
% 9.52/3.10  tff(c_1667, plain, (![B_54]: (~r2_hidden('#skF_8', k3_xboole_0(B_54, k1_tarski('#skF_10'))))), inference(resolution, [status(thm)], [c_96, c_1644])).
% 9.52/3.10  tff(c_60, plain, ('#skF_7'!='#skF_5' | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.52/3.10  tff(c_145, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_60])).
% 9.52/3.10  tff(c_28, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.52/3.10  tff(c_378, plain, (![A_111, B_112, C_113]: (r2_hidden(A_111, B_112) | r2_hidden(A_111, C_113) | ~r2_hidden(A_111, k5_xboole_0(B_112, C_113)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.52/3.10  tff(c_2963, plain, (![A_4070, A_4071, B_4072]: (r2_hidden(A_4070, A_4071) | r2_hidden(A_4070, k3_xboole_0(A_4071, B_4072)) | ~r2_hidden(A_4070, k4_xboole_0(A_4071, B_4072)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_378])).
% 9.52/3.10  tff(c_2989, plain, (r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(resolution, [status(thm)], [c_187, c_2963])).
% 9.52/3.10  tff(c_3011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1667, c_145, c_2989])).
% 9.52/3.10  tff(c_3012, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 9.52/3.10  tff(c_3781, plain, (![A_5837, C_5838, B_5839]: (r2_hidden(A_5837, C_5838) | ~r2_hidden(A_5837, B_5839) | r2_hidden(A_5837, k5_xboole_0(B_5839, C_5838)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.52/3.10  tff(c_5322, plain, (![A_8275, A_8276, B_8277]: (r2_hidden(A_8275, k3_xboole_0(A_8276, B_8277)) | ~r2_hidden(A_8275, A_8276) | r2_hidden(A_8275, k4_xboole_0(A_8276, B_8277)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_3781])).
% 9.52/3.10  tff(c_3013, plain, (~r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_68])).
% 9.52/3.10  tff(c_64, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.52/3.10  tff(c_3092, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_3013, c_64])).
% 9.52/3.10  tff(c_5370, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_5322, c_3092])).
% 9.52/3.10  tff(c_5398, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_3012, c_5370])).
% 9.52/3.10  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.52/3.10  tff(c_5464, plain, (![B_8362]: (r2_hidden('#skF_5', B_8362) | ~r1_tarski(k3_xboole_0('#skF_6', k1_tarski('#skF_7')), B_8362))), inference(resolution, [status(thm)], [c_5398, c_4])).
% 9.52/3.10  tff(c_5484, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_96, c_5464])).
% 9.52/3.10  tff(c_34, plain, (![C_26, A_22]: (C_26=A_22 | ~r2_hidden(C_26, k1_tarski(A_22)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.52/3.10  tff(c_5502, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_5484, c_34])).
% 9.52/3.10  tff(c_5562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_5502])).
% 9.52/3.10  tff(c_5563, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_66])).
% 9.52/3.10  tff(c_5608, plain, (![C_8452, B_8453, A_8454]: (r2_hidden(C_8452, B_8453) | ~r2_hidden(C_8452, A_8454) | ~r1_tarski(A_8454, B_8453))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.52/3.10  tff(c_5622, plain, (![A_11, B_12, B_8453]: (r2_hidden('#skF_2'(A_11, B_12), B_8453) | ~r1_tarski(A_11, B_8453) | r1_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_26, c_5608])).
% 9.52/3.10  tff(c_5631, plain, (![A_8457, B_8458, C_8459]: (~r1_xboole_0(A_8457, B_8458) | ~r2_hidden(C_8459, B_8458) | ~r2_hidden(C_8459, A_8457))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.52/3.10  tff(c_5636, plain, (![C_8460, B_8461, A_8462]: (~r2_hidden(C_8460, B_8461) | ~r2_hidden(C_8460, k4_xboole_0(A_8462, B_8461)))), inference(resolution, [status(thm)], [c_32, c_5631])).
% 9.52/3.10  tff(c_7105, plain, (![A_10965, A_10966, B_10967]: (~r2_hidden('#skF_2'(A_10965, k4_xboole_0(A_10966, B_10967)), B_10967) | r1_xboole_0(A_10965, k4_xboole_0(A_10966, B_10967)))), inference(resolution, [status(thm)], [c_24, c_5636])).
% 9.52/3.10  tff(c_7166, plain, (![A_11054, B_11055, A_11056]: (~r1_tarski(A_11054, B_11055) | r1_xboole_0(A_11054, k4_xboole_0(A_11056, B_11055)))), inference(resolution, [status(thm)], [c_5622, c_7105])).
% 9.52/3.10  tff(c_7274, plain, (![C_11233, A_11234, B_11235, A_11236]: (~r2_hidden(C_11233, k4_xboole_0(A_11234, B_11235)) | ~r2_hidden(C_11233, A_11236) | ~r1_tarski(A_11236, B_11235))), inference(resolution, [status(thm)], [c_7166, c_22])).
% 9.52/3.10  tff(c_7307, plain, (![A_11279]: (~r2_hidden('#skF_8', A_11279) | ~r1_tarski(A_11279, k1_tarski('#skF_10')))), inference(resolution, [status(thm)], [c_5563, c_7274])).
% 9.52/3.10  tff(c_7330, plain, (![B_54]: (~r2_hidden('#skF_8', k3_xboole_0(B_54, k1_tarski('#skF_10'))))), inference(resolution, [status(thm)], [c_96, c_7307])).
% 9.52/3.10  tff(c_5734, plain, (![A_8478, B_8479, C_8480]: (r2_hidden(A_8478, B_8479) | r2_hidden(A_8478, C_8480) | ~r2_hidden(A_8478, k5_xboole_0(B_8479, C_8480)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.52/3.10  tff(c_8006, plain, (![A_12162, A_12163, B_12164]: (r2_hidden(A_12162, A_12163) | r2_hidden(A_12162, k3_xboole_0(A_12163, B_12164)) | ~r2_hidden(A_12162, k4_xboole_0(A_12163, B_12164)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_5734])).
% 9.52/3.10  tff(c_8029, plain, (r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(resolution, [status(thm)], [c_5563, c_8006])).
% 9.52/3.10  tff(c_8050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7330, c_145, c_8029])).
% 9.52/3.10  tff(c_8051, plain, ('#skF_7'!='#skF_5' | '#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_60])).
% 9.52/3.10  tff(c_8053, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_8051])).
% 9.52/3.10  tff(c_8052, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_60])).
% 9.52/3.10  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_6') | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.52/3.10  tff(c_8055, plain, (r2_hidden('#skF_5', '#skF_6') | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8052, c_62])).
% 9.52/3.10  tff(c_8056, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_8055])).
% 9.52/3.10  tff(c_8129, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_8056, c_68])).
% 9.52/3.10  tff(c_8130, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_8129])).
% 9.52/3.10  tff(c_8141, plain, (![A_12223, B_12224, C_12225]: (~r1_xboole_0(A_12223, B_12224) | ~r2_hidden(C_12225, B_12224) | ~r2_hidden(C_12225, A_12223))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.52/3.10  tff(c_8145, plain, (![C_12226, B_12227, A_12228]: (~r2_hidden(C_12226, B_12227) | ~r2_hidden(C_12226, k4_xboole_0(A_12228, B_12227)))), inference(resolution, [status(thm)], [c_32, c_8141])).
% 9.52/3.10  tff(c_8148, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_8130, c_8145])).
% 9.52/3.10  tff(c_8164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_8148])).
% 9.52/3.10  tff(c_8165, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_8129])).
% 9.52/3.10  tff(c_9031, plain, (![A_14430, C_14431, B_14432]: (r2_hidden(A_14430, C_14431) | ~r2_hidden(A_14430, B_14432) | r2_hidden(A_14430, k5_xboole_0(B_14432, C_14431)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.52/3.10  tff(c_11083, plain, (![A_17708, A_17709, B_17710]: (r2_hidden(A_17708, k3_xboole_0(A_17709, B_17710)) | ~r2_hidden(A_17708, A_17709) | r2_hidden(A_17708, k4_xboole_0(A_17709, B_17710)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_9031])).
% 9.52/3.10  tff(c_8166, plain, (~r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_8129])).
% 9.52/3.10  tff(c_8284, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_8056, c_64])).
% 9.52/3.10  tff(c_8285, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_8166, c_8284])).
% 9.52/3.10  tff(c_11139, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_11083, c_8285])).
% 9.52/3.10  tff(c_11172, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_8165, c_11139])).
% 9.52/3.10  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.52/3.10  tff(c_9007, plain, (![A_14385, B_14386, C_14387]: (r2_hidden(A_14385, B_14386) | ~r2_hidden(A_14385, C_14387) | r2_hidden(A_14385, k5_xboole_0(B_14386, C_14387)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.52/3.10  tff(c_10453, plain, (![A_16949, A_16950, B_16951]: (r2_hidden(A_16949, A_16950) | ~r2_hidden(A_16949, k3_xboole_0(A_16950, B_16951)) | r2_hidden(A_16949, k4_xboole_0(A_16950, B_16951)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_9007])).
% 9.52/3.10  tff(c_8179, plain, (![A_12232, B_12233, C_12234]: (~r1_xboole_0(A_12232, B_12233) | ~r2_hidden(C_12234, B_12233) | ~r2_hidden(C_12234, A_12232))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.52/3.10  tff(c_8182, plain, (![C_12234, B_21, A_20]: (~r2_hidden(C_12234, B_21) | ~r2_hidden(C_12234, k4_xboole_0(A_20, B_21)))), inference(resolution, [status(thm)], [c_32, c_8179])).
% 9.52/3.10  tff(c_10535, plain, (![A_16994, B_16995, A_16996]: (~r2_hidden(A_16994, B_16995) | r2_hidden(A_16994, A_16996) | ~r2_hidden(A_16994, k3_xboole_0(A_16996, B_16995)))), inference(resolution, [status(thm)], [c_10453, c_8182])).
% 9.52/3.10  tff(c_10575, plain, (![A_16994, B_2, A_1]: (~r2_hidden(A_16994, B_2) | r2_hidden(A_16994, A_1) | ~r2_hidden(A_16994, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10535])).
% 9.52/3.10  tff(c_11271, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_11172, c_10575])).
% 9.52/3.10  tff(c_11339, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_8165, c_11271])).
% 9.52/3.10  tff(c_11361, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_11339, c_34])).
% 9.52/3.10  tff(c_11420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8053, c_11361])).
% 9.52/3.10  tff(c_11421, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_8055])).
% 9.52/3.10  tff(c_11736, plain, (![A_17946, C_17947, B_17948]: (r2_hidden(A_17946, C_17947) | ~r2_hidden(A_17946, B_17948) | r2_hidden(A_17946, k5_xboole_0(B_17948, C_17947)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.52/3.10  tff(c_14825, plain, (![A_23763, A_23764, B_23765]: (r2_hidden(A_23763, k3_xboole_0(A_23764, B_23765)) | ~r2_hidden(A_23763, A_23764) | r2_hidden(A_23763, k4_xboole_0(A_23764, B_23765)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_11736])).
% 9.52/3.10  tff(c_11422, plain, ('#skF_10'!='#skF_8'), inference(splitRight, [status(thm)], [c_8055])).
% 9.52/3.10  tff(c_58, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.52/3.10  tff(c_11569, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8052, c_58])).
% 9.52/3.10  tff(c_11570, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_11422, c_11569])).
% 9.52/3.10  tff(c_14873, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_14825, c_11570])).
% 9.52/3.10  tff(c_14899, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_11421, c_14873])).
% 9.52/3.10  tff(c_11717, plain, (![A_17943, B_17944, C_17945]: (r2_hidden(A_17943, B_17944) | ~r2_hidden(A_17943, C_17945) | r2_hidden(A_17943, k5_xboole_0(B_17944, C_17945)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.52/3.10  tff(c_13743, plain, (![A_22221, A_22222, B_22223]: (r2_hidden(A_22221, A_22222) | ~r2_hidden(A_22221, k3_xboole_0(A_22222, B_22223)) | r2_hidden(A_22221, k4_xboole_0(A_22222, B_22223)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_11717])).
% 9.52/3.10  tff(c_11530, plain, (![A_17898, B_17899, C_17900]: (~r1_xboole_0(A_17898, B_17899) | ~r2_hidden(C_17900, B_17899) | ~r2_hidden(C_17900, A_17898))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.52/3.10  tff(c_11542, plain, (![C_17904, B_17905, A_17906]: (~r2_hidden(C_17904, B_17905) | ~r2_hidden(C_17904, k4_xboole_0(A_17906, B_17905)))), inference(resolution, [status(thm)], [c_32, c_11530])).
% 9.52/3.10  tff(c_13449, plain, (![A_21460, A_21461, B_21462]: (~r2_hidden('#skF_2'(A_21460, k4_xboole_0(A_21461, B_21462)), B_21462) | r1_xboole_0(A_21460, k4_xboole_0(A_21461, B_21462)))), inference(resolution, [status(thm)], [c_24, c_11542])).
% 9.52/3.10  tff(c_13531, plain, (![A_21549, A_21550]: (r1_xboole_0(A_21549, k4_xboole_0(A_21550, A_21549)))), inference(resolution, [status(thm)], [c_26, c_13449])).
% 9.52/3.10  tff(c_13535, plain, (![C_15, A_21550, A_21549]: (~r2_hidden(C_15, k4_xboole_0(A_21550, A_21549)) | ~r2_hidden(C_15, A_21549))), inference(resolution, [status(thm)], [c_13531, c_22])).
% 9.52/3.10  tff(c_13798, plain, (![A_22266, B_22267, A_22268]: (~r2_hidden(A_22266, B_22267) | r2_hidden(A_22266, A_22268) | ~r2_hidden(A_22266, k3_xboole_0(A_22268, B_22267)))), inference(resolution, [status(thm)], [c_13743, c_13535])).
% 9.52/3.10  tff(c_13841, plain, (![A_22266, A_1, B_2]: (~r2_hidden(A_22266, A_1) | r2_hidden(A_22266, B_2) | ~r2_hidden(A_22266, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_13798])).
% 9.52/3.10  tff(c_14906, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_14899, c_13841])).
% 9.52/3.10  tff(c_14970, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_11421, c_14906])).
% 9.52/3.10  tff(c_14995, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_14970, c_34])).
% 9.52/3.10  tff(c_15056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8053, c_14995])).
% 9.52/3.10  tff(c_15057, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_8051])).
% 9.52/3.10  tff(c_15058, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_8051])).
% 9.52/3.10  tff(c_15072, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_15057, c_15058, c_66])).
% 9.52/3.10  tff(c_15170, plain, (![A_23953, B_23954, C_23955]: (~r1_xboole_0(A_23953, B_23954) | ~r2_hidden(C_23955, B_23954) | ~r2_hidden(C_23955, A_23953))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.52/3.10  tff(c_15193, plain, (![C_23960, B_23961, A_23962]: (~r2_hidden(C_23960, B_23961) | ~r2_hidden(C_23960, k4_xboole_0(A_23962, B_23961)))), inference(resolution, [status(thm)], [c_32, c_15170])).
% 9.52/3.10  tff(c_15212, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_15072, c_15193])).
% 9.52/3.10  tff(c_15220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_15212])).
% 9.52/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.52/3.10  
% 9.52/3.10  Inference rules
% 9.52/3.10  ----------------------
% 9.52/3.10  #Ref     : 0
% 9.52/3.10  #Sup     : 2534
% 9.52/3.10  #Fact    : 0
% 9.52/3.10  #Define  : 0
% 9.52/3.10  #Split   : 26
% 9.52/3.10  #Chain   : 0
% 9.52/3.10  #Close   : 0
% 9.52/3.10  
% 9.52/3.10  Ordering : KBO
% 9.52/3.10  
% 9.52/3.10  Simplification rules
% 9.52/3.10  ----------------------
% 9.52/3.10  #Subsume      : 243
% 9.52/3.10  #Demod        : 225
% 9.52/3.10  #Tautology    : 352
% 9.52/3.10  #SimpNegUnit  : 8
% 9.52/3.10  #BackRed      : 0
% 9.52/3.10  
% 9.52/3.10  #Partial instantiations: 10860
% 9.52/3.10  #Strategies tried      : 1
% 9.52/3.10  
% 9.52/3.10  Timing (in seconds)
% 9.52/3.10  ----------------------
% 9.52/3.10  Preprocessing        : 0.34
% 9.52/3.10  Parsing              : 0.18
% 9.52/3.10  CNF conversion       : 0.03
% 9.52/3.10  Main loop            : 1.93
% 9.52/3.10  Inferencing          : 0.88
% 9.52/3.10  Reduction            : 0.44
% 9.52/3.10  Demodulation         : 0.30
% 9.52/3.10  BG Simplification    : 0.08
% 9.52/3.10  Subsumption          : 0.38
% 9.52/3.10  Abstraction          : 0.08
% 9.52/3.10  MUC search           : 0.00
% 9.52/3.10  Cooper               : 0.00
% 9.52/3.10  Total                : 2.32
% 9.52/3.10  Index Insertion      : 0.00
% 9.52/3.10  Index Deletion       : 0.00
% 9.52/3.10  Index Matching       : 0.00
% 9.52/3.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
