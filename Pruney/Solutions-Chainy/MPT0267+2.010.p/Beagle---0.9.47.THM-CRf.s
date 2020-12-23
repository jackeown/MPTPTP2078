%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:33 EST 2020

% Result     : Theorem 6.19s
% Output     : CNFRefutation 6.19s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 239 expanded)
%              Number of leaves         :   30 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :  153 ( 454 expanded)
%              Number of equality atoms :   25 ( 138 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
      <=> ( r2_hidden(A,B)
          & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_62,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,
    ( '#skF_7' != '#skF_5'
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_107,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_70,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_109,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_32,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_157,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden(A_78,B_79)
      | r2_hidden(A_78,C_80)
      | ~ r2_hidden(A_78,k5_xboole_0(B_79,C_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_823,plain,(
    ! [A_2046,A_2047,B_2048] :
      ( r2_hidden(A_2046,A_2047)
      | r2_hidden(A_2046,k3_xboole_0(A_2047,B_2048))
      | ~ r2_hidden(A_2046,k4_xboole_0(A_2047,B_2048)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_157])).

tff(c_834,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_109,c_823])).

tff(c_839,plain,(
    r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_834])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_857,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_839,c_6])).

tff(c_915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_857])).

tff(c_916,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_936,plain,(
    ! [A_2217,C_2218,B_2219] :
      ( r2_hidden(A_2217,C_2218)
      | ~ r2_hidden(A_2217,B_2219)
      | r2_hidden(A_2217,k5_xboole_0(B_2219,C_2218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1596,plain,(
    ! [A_4244,A_4245,B_4246] :
      ( r2_hidden(A_4244,k3_xboole_0(A_4245,B_4246))
      | ~ r2_hidden(A_4244,A_4245)
      | r2_hidden(A_4244,k4_xboole_0(A_4245,B_4246)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_936])).

tff(c_917,plain,(
    ~ r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1217,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_917,c_66])).

tff(c_1616,plain,
    ( r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1596,c_1217])).

tff(c_1628,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_1616])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1691,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1628,c_4])).

tff(c_34,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1707,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1691,c_34])).

tff(c_1763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1707])).

tff(c_1764,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1808,plain,(
    ! [A_4475,B_4476,C_4477] :
      ( r2_hidden(A_4475,B_4476)
      | r2_hidden(A_4475,C_4477)
      | ~ r2_hidden(A_4475,k5_xboole_0(B_4476,C_4477)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2323,plain,(
    ! [A_6007,A_6008,B_6009] :
      ( r2_hidden(A_6007,A_6008)
      | r2_hidden(A_6007,k3_xboole_0(A_6008,B_6009))
      | ~ r2_hidden(A_6007,k4_xboole_0(A_6008,B_6009)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1808])).

tff(c_2331,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_1764,c_2323])).

tff(c_2335,plain,(
    r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_2331])).

tff(c_2341,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_2335,c_6])).

tff(c_2398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_2341])).

tff(c_2400,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_36,plain,(
    ! [C_16] : r2_hidden(C_16,k1_tarski(C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2401,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_64,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2421,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2400,c_64])).

tff(c_2422,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2421])).

tff(c_2429,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_70])).

tff(c_2430,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_2429])).

tff(c_2446,plain,(
    ! [A_6130,C_6131,B_6132] :
      ( ~ r2_hidden(A_6130,C_6131)
      | ~ r2_hidden(A_6130,B_6132)
      | ~ r2_hidden(A_6130,k5_xboole_0(B_6132,C_6131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2991,plain,(
    ! [A_7779,A_7780,B_7781] :
      ( ~ r2_hidden(A_7779,k3_xboole_0(A_7780,B_7781))
      | ~ r2_hidden(A_7779,A_7780)
      | ~ r2_hidden(A_7779,k4_xboole_0(A_7780,B_7781)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2446])).

tff(c_3002,plain,
    ( ~ r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_2430,c_2991])).

tff(c_3007,plain,(
    ~ r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2400,c_3002])).

tff(c_3020,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_2,c_3007])).

tff(c_3029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2400,c_36,c_3020])).

tff(c_3030,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2429])).

tff(c_3322,plain,(
    ! [A_9005,C_9006,B_9007] :
      ( r2_hidden(A_9005,C_9006)
      | ~ r2_hidden(A_9005,B_9007)
      | r2_hidden(A_9005,k5_xboole_0(B_9007,C_9006)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3539,plain,(
    ! [A_9649,A_9650,B_9651] :
      ( r2_hidden(A_9649,k3_xboole_0(A_9650,B_9651))
      | ~ r2_hidden(A_9649,A_9650)
      | r2_hidden(A_9649,k4_xboole_0(A_9650,B_9651)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3322])).

tff(c_3031,plain,(
    ~ r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_2429])).

tff(c_3336,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2422,c_66])).

tff(c_3337,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3031,c_3336])).

tff(c_3554,plain,
    ( r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_3539,c_3337])).

tff(c_3566,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3030,c_3554])).

tff(c_3691,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3566,c_4])).

tff(c_3697,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3691,c_34])).

tff(c_3752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2401,c_3697])).

tff(c_3753,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2421])).

tff(c_4046,plain,(
    ! [A_10927,C_10928,B_10929] :
      ( r2_hidden(A_10927,C_10928)
      | ~ r2_hidden(A_10927,B_10929)
      | r2_hidden(A_10927,k5_xboole_0(B_10929,C_10928)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4434,plain,(
    ! [A_11787,A_11788,B_11789] :
      ( r2_hidden(A_11787,k3_xboole_0(A_11788,B_11789))
      | ~ r2_hidden(A_11787,A_11788)
      | r2_hidden(A_11787,k4_xboole_0(A_11788,B_11789)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4046])).

tff(c_3754,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2421])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3759,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2400,c_60])).

tff(c_3760,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3754,c_3759])).

tff(c_4451,plain,
    ( r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_4434,c_3760])).

tff(c_4461,plain,(
    r2_hidden('#skF_5',k3_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3753,c_4451])).

tff(c_4535,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4461,c_4])).

tff(c_4540,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4535,c_34])).

tff(c_4596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2401,c_4540])).

tff(c_4598,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2399,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_4610,plain,(
    '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4598,c_2399])).

tff(c_4597,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_4616,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4610,c_4597])).

tff(c_4647,plain,(
    ! [A_12017,C_12018,B_12019] :
      ( ~ r2_hidden(A_12017,C_12018)
      | ~ r2_hidden(A_12017,B_12019)
      | ~ r2_hidden(A_12017,k5_xboole_0(B_12019,C_12018)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5515,plain,(
    ! [A_14155,A_14156,B_14157] :
      ( ~ r2_hidden(A_14155,k3_xboole_0(A_14156,B_14157))
      | ~ r2_hidden(A_14155,A_14156)
      | ~ r2_hidden(A_14155,k4_xboole_0(A_14156,B_14157)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4647])).

tff(c_5534,plain,
    ( ~ r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_8')))
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_4616,c_5515])).

tff(c_5541,plain,(
    ~ r2_hidden('#skF_8',k3_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2400,c_5534])).

tff(c_5549,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_2,c_5541])).

tff(c_5553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2400,c_36,c_5549])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.19/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.19  
% 6.19/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.19  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 6.19/2.19  
% 6.19/2.19  %Foreground sorts:
% 6.19/2.19  
% 6.19/2.19  
% 6.19/2.19  %Background operators:
% 6.19/2.19  
% 6.19/2.19  
% 6.19/2.19  %Foreground operators:
% 6.19/2.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.19/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.19/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.19/2.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.19/2.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.19/2.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.19/2.19  tff('#skF_7', type, '#skF_7': $i).
% 6.19/2.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.19/2.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.19/2.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.19/2.19  tff('#skF_10', type, '#skF_10': $i).
% 6.19/2.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.19/2.19  tff('#skF_5', type, '#skF_5': $i).
% 6.19/2.19  tff('#skF_6', type, '#skF_6': $i).
% 6.19/2.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.19/2.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.19/2.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.19/2.19  tff('#skF_9', type, '#skF_9': $i).
% 6.19/2.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.19/2.19  tff('#skF_8', type, '#skF_8': $i).
% 6.19/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.19/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.19/2.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.19/2.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.19/2.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.19/2.19  
% 6.19/2.21  tff(f_72, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 6.19/2.21  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.19/2.21  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.19/2.21  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.19/2.21  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 6.19/2.21  tff(c_62, plain, ('#skF_7'!='#skF_5' | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.19/2.21  tff(c_87, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_62])).
% 6.19/2.21  tff(c_68, plain, ('#skF_7'!='#skF_5' | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.19/2.21  tff(c_107, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_68])).
% 6.19/2.21  tff(c_70, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.19/2.21  tff(c_109, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_70])).
% 6.19/2.21  tff(c_32, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.19/2.21  tff(c_157, plain, (![A_78, B_79, C_80]: (r2_hidden(A_78, B_79) | r2_hidden(A_78, C_80) | ~r2_hidden(A_78, k5_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.19/2.21  tff(c_823, plain, (![A_2046, A_2047, B_2048]: (r2_hidden(A_2046, A_2047) | r2_hidden(A_2046, k3_xboole_0(A_2047, B_2048)) | ~r2_hidden(A_2046, k4_xboole_0(A_2047, B_2048)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_157])).
% 6.19/2.21  tff(c_834, plain, (r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(resolution, [status(thm)], [c_109, c_823])).
% 6.19/2.21  tff(c_839, plain, (r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_87, c_834])).
% 6.19/2.21  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.19/2.21  tff(c_857, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_839, c_6])).
% 6.19/2.21  tff(c_915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_857])).
% 6.19/2.21  tff(c_916, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 6.19/2.21  tff(c_936, plain, (![A_2217, C_2218, B_2219]: (r2_hidden(A_2217, C_2218) | ~r2_hidden(A_2217, B_2219) | r2_hidden(A_2217, k5_xboole_0(B_2219, C_2218)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.19/2.21  tff(c_1596, plain, (![A_4244, A_4245, B_4246]: (r2_hidden(A_4244, k3_xboole_0(A_4245, B_4246)) | ~r2_hidden(A_4244, A_4245) | r2_hidden(A_4244, k4_xboole_0(A_4245, B_4246)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_936])).
% 6.19/2.21  tff(c_917, plain, (~r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_70])).
% 6.19/2.21  tff(c_66, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.19/2.21  tff(c_1217, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_917, c_66])).
% 6.19/2.21  tff(c_1616, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1596, c_1217])).
% 6.19/2.21  tff(c_1628, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_916, c_1616])).
% 6.19/2.21  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.19/2.21  tff(c_1691, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_1628, c_4])).
% 6.19/2.21  tff(c_34, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.19/2.21  tff(c_1707, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1691, c_34])).
% 6.19/2.21  tff(c_1763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_1707])).
% 6.19/2.21  tff(c_1764, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_68])).
% 6.19/2.21  tff(c_1808, plain, (![A_4475, B_4476, C_4477]: (r2_hidden(A_4475, B_4476) | r2_hidden(A_4475, C_4477) | ~r2_hidden(A_4475, k5_xboole_0(B_4476, C_4477)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.19/2.21  tff(c_2323, plain, (![A_6007, A_6008, B_6009]: (r2_hidden(A_6007, A_6008) | r2_hidden(A_6007, k3_xboole_0(A_6008, B_6009)) | ~r2_hidden(A_6007, k4_xboole_0(A_6008, B_6009)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1808])).
% 6.19/2.21  tff(c_2331, plain, (r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(resolution, [status(thm)], [c_1764, c_2323])).
% 6.19/2.21  tff(c_2335, plain, (r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_87, c_2331])).
% 6.19/2.21  tff(c_2341, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_2335, c_6])).
% 6.19/2.21  tff(c_2398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_2341])).
% 6.19/2.21  tff(c_2400, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_62])).
% 6.19/2.21  tff(c_36, plain, (![C_16]: (r2_hidden(C_16, k1_tarski(C_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.19/2.21  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.19/2.21  tff(c_2401, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_68])).
% 6.19/2.21  tff(c_64, plain, (r2_hidden('#skF_5', '#skF_6') | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.19/2.21  tff(c_2421, plain, (r2_hidden('#skF_5', '#skF_6') | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2400, c_64])).
% 6.19/2.21  tff(c_2422, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_2421])).
% 6.19/2.21  tff(c_2429, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_70])).
% 6.19/2.21  tff(c_2430, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_2429])).
% 6.19/2.21  tff(c_2446, plain, (![A_6130, C_6131, B_6132]: (~r2_hidden(A_6130, C_6131) | ~r2_hidden(A_6130, B_6132) | ~r2_hidden(A_6130, k5_xboole_0(B_6132, C_6131)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.19/2.21  tff(c_2991, plain, (![A_7779, A_7780, B_7781]: (~r2_hidden(A_7779, k3_xboole_0(A_7780, B_7781)) | ~r2_hidden(A_7779, A_7780) | ~r2_hidden(A_7779, k4_xboole_0(A_7780, B_7781)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2446])).
% 6.19/2.21  tff(c_3002, plain, (~r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_8'))) | ~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_2430, c_2991])).
% 6.19/2.21  tff(c_3007, plain, (~r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_2400, c_3002])).
% 6.19/2.21  tff(c_3020, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | ~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_2, c_3007])).
% 6.19/2.21  tff(c_3029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2400, c_36, c_3020])).
% 6.19/2.21  tff(c_3030, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_2429])).
% 6.19/2.21  tff(c_3322, plain, (![A_9005, C_9006, B_9007]: (r2_hidden(A_9005, C_9006) | ~r2_hidden(A_9005, B_9007) | r2_hidden(A_9005, k5_xboole_0(B_9007, C_9006)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.19/2.21  tff(c_3539, plain, (![A_9649, A_9650, B_9651]: (r2_hidden(A_9649, k3_xboole_0(A_9650, B_9651)) | ~r2_hidden(A_9649, A_9650) | r2_hidden(A_9649, k4_xboole_0(A_9650, B_9651)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_3322])).
% 6.19/2.21  tff(c_3031, plain, (~r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_2429])).
% 6.19/2.21  tff(c_3336, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_2422, c_66])).
% 6.19/2.21  tff(c_3337, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_3031, c_3336])).
% 6.19/2.21  tff(c_3554, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_3539, c_3337])).
% 6.19/2.21  tff(c_3566, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_3030, c_3554])).
% 6.19/2.21  tff(c_3691, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_3566, c_4])).
% 6.19/2.21  tff(c_3697, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_3691, c_34])).
% 6.19/2.21  tff(c_3752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2401, c_3697])).
% 6.19/2.21  tff(c_3753, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_2421])).
% 6.19/2.21  tff(c_4046, plain, (![A_10927, C_10928, B_10929]: (r2_hidden(A_10927, C_10928) | ~r2_hidden(A_10927, B_10929) | r2_hidden(A_10927, k5_xboole_0(B_10929, C_10928)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.19/2.21  tff(c_4434, plain, (![A_11787, A_11788, B_11789]: (r2_hidden(A_11787, k3_xboole_0(A_11788, B_11789)) | ~r2_hidden(A_11787, A_11788) | r2_hidden(A_11787, k4_xboole_0(A_11788, B_11789)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_4046])).
% 6.19/2.21  tff(c_3754, plain, ('#skF_10'!='#skF_8'), inference(splitRight, [status(thm)], [c_2421])).
% 6.19/2.21  tff(c_60, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.19/2.21  tff(c_3759, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2400, c_60])).
% 6.19/2.21  tff(c_3760, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_3754, c_3759])).
% 6.19/2.21  tff(c_4451, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7'))) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_4434, c_3760])).
% 6.19/2.21  tff(c_4461, plain, (r2_hidden('#skF_5', k3_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_3753, c_4451])).
% 6.19/2.21  tff(c_4535, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_4461, c_4])).
% 6.19/2.21  tff(c_4540, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_4535, c_34])).
% 6.19/2.21  tff(c_4596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2401, c_4540])).
% 6.19/2.21  tff(c_4598, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_68])).
% 6.19/2.21  tff(c_2399, plain, ('#skF_7'!='#skF_5' | '#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_62])).
% 6.19/2.21  tff(c_4610, plain, ('#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4598, c_2399])).
% 6.19/2.21  tff(c_4597, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_68])).
% 6.19/2.21  tff(c_4616, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_4610, c_4597])).
% 6.19/2.21  tff(c_4647, plain, (![A_12017, C_12018, B_12019]: (~r2_hidden(A_12017, C_12018) | ~r2_hidden(A_12017, B_12019) | ~r2_hidden(A_12017, k5_xboole_0(B_12019, C_12018)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.19/2.21  tff(c_5515, plain, (![A_14155, A_14156, B_14157]: (~r2_hidden(A_14155, k3_xboole_0(A_14156, B_14157)) | ~r2_hidden(A_14155, A_14156) | ~r2_hidden(A_14155, k4_xboole_0(A_14156, B_14157)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_4647])).
% 6.19/2.21  tff(c_5534, plain, (~r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_8'))) | ~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_4616, c_5515])).
% 6.19/2.21  tff(c_5541, plain, (~r2_hidden('#skF_8', k3_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_2400, c_5534])).
% 6.19/2.21  tff(c_5549, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | ~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_2, c_5541])).
% 6.19/2.21  tff(c_5553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2400, c_36, c_5549])).
% 6.19/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.21  
% 6.19/2.21  Inference rules
% 6.19/2.21  ----------------------
% 6.19/2.21  #Ref     : 0
% 6.19/2.21  #Sup     : 751
% 6.19/2.21  #Fact    : 0
% 6.19/2.21  #Define  : 0
% 6.19/2.21  #Split   : 17
% 6.19/2.21  #Chain   : 0
% 6.19/2.21  #Close   : 0
% 6.19/2.21  
% 6.19/2.21  Ordering : KBO
% 6.19/2.21  
% 6.19/2.21  Simplification rules
% 6.19/2.21  ----------------------
% 6.19/2.21  #Subsume      : 37
% 6.19/2.21  #Demod        : 123
% 6.19/2.21  #Tautology    : 185
% 6.19/2.21  #SimpNegUnit  : 10
% 6.19/2.21  #BackRed      : 0
% 6.19/2.21  
% 6.19/2.21  #Partial instantiations: 5544
% 6.19/2.21  #Strategies tried      : 1
% 6.19/2.21  
% 6.19/2.21  Timing (in seconds)
% 6.19/2.21  ----------------------
% 6.19/2.21  Preprocessing        : 0.33
% 6.19/2.21  Parsing              : 0.16
% 6.19/2.21  CNF conversion       : 0.03
% 6.19/2.21  Main loop            : 1.10
% 6.19/2.21  Inferencing          : 0.58
% 6.19/2.21  Reduction            : 0.22
% 6.19/2.21  Demodulation         : 0.15
% 6.19/2.21  BG Simplification    : 0.05
% 6.19/2.21  Subsumption          : 0.16
% 6.19/2.21  Abstraction          : 0.05
% 6.19/2.21  MUC search           : 0.00
% 6.19/2.21  Cooper               : 0.00
% 6.19/2.21  Total                : 1.47
% 6.19/2.21  Index Insertion      : 0.00
% 6.19/2.21  Index Deletion       : 0.00
% 6.19/2.21  Index Matching       : 0.00
% 6.19/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
