%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:17 EST 2020

% Result     : Theorem 11.83s
% Output     : CNFRefutation 11.95s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 173 expanded)
%              Number of leaves         :   41 (  73 expanded)
%              Depth                    :    8
%              Number of atoms          :  157 ( 283 expanded)
%              Number of equality atoms :   44 (  89 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_75,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_73,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(c_96,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_10','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_265,plain,(
    ~ r2_hidden('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_238,plain,(
    ! [A_75,B_76] : k1_enumset1(A_75,A_75,B_76) = k2_tarski(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    ! [E_33,B_28,C_29] : r2_hidden(E_33,k1_enumset1(E_33,B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_244,plain,(
    ! [A_75,B_76] : r2_hidden(A_75,k2_tarski(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_62])).

tff(c_54,plain,(
    ! [A_26] : r1_xboole_0(A_26,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,(
    ! [A_25] : k3_xboole_0(A_25,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_307,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r1_xboole_0(A_88,B_89)
      | ~ r2_hidden(C_90,k3_xboole_0(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_319,plain,(
    ! [A_25,C_90] :
      ( ~ r1_xboole_0(A_25,k1_xboole_0)
      | ~ r2_hidden(C_90,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_307])).

tff(c_324,plain,(
    ! [C_90] : ~ r2_hidden(C_90,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_319])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_102,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_225,plain,(
    k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_50,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_868,plain,(
    ! [A_151,C_152,B_153] :
      ( r2_hidden(A_151,C_152)
      | ~ r2_hidden(A_151,B_153)
      | r2_hidden(A_151,k5_xboole_0(B_153,C_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8304,plain,(
    ! [A_17484,A_17485,B_17486] :
      ( r2_hidden(A_17484,k3_xboole_0(A_17485,B_17486))
      | ~ r2_hidden(A_17484,A_17485)
      | r2_hidden(A_17484,k4_xboole_0(A_17485,B_17486)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_868])).

tff(c_8364,plain,(
    ! [A_17484] :
      ( r2_hidden(A_17484,k3_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11'))
      | ~ r2_hidden(A_17484,k2_tarski('#skF_9','#skF_10'))
      | r2_hidden(A_17484,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_8304])).

tff(c_8385,plain,(
    ! [A_17484] :
      ( r2_hidden(A_17484,k3_xboole_0('#skF_11',k2_tarski('#skF_9','#skF_10')))
      | ~ r2_hidden(A_17484,k2_tarski('#skF_9','#skF_10'))
      | r2_hidden(A_17484,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8364])).

tff(c_8387,plain,(
    ! [A_17634] :
      ( r2_hidden(A_17634,k3_xboole_0('#skF_11',k2_tarski('#skF_9','#skF_10')))
      | ~ r2_hidden(A_17634,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_324,c_8385])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8450,plain,(
    ! [A_17782] :
      ( r2_hidden(A_17782,'#skF_11')
      | ~ r2_hidden(A_17782,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_8387,c_8])).

tff(c_8506,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_244,c_8450])).

tff(c_8523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_8506])).

tff(c_8524,plain,
    ( ~ r2_hidden('#skF_10','#skF_11')
    | r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_8527,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_8524])).

tff(c_58,plain,(
    ! [E_33,A_27,B_28] : r2_hidden(E_33,k1_enumset1(A_27,B_28,E_33)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_247,plain,(
    ! [B_76,A_75] : r2_hidden(B_76,k2_tarski(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_58])).

tff(c_8550,plain,(
    ! [A_17937,B_17938,C_17939] :
      ( ~ r1_xboole_0(A_17937,B_17938)
      | ~ r2_hidden(C_17939,k3_xboole_0(A_17937,B_17938)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8562,plain,(
    ! [A_25,C_17939] :
      ( ~ r1_xboole_0(A_25,k1_xboole_0)
      | ~ r2_hidden(C_17939,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_8550])).

tff(c_8567,plain,(
    ! [C_17939] : ~ r2_hidden(C_17939,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8562])).

tff(c_9260,plain,(
    ! [A_18015,C_18016,B_18017] :
      ( r2_hidden(A_18015,C_18016)
      | ~ r2_hidden(A_18015,B_18017)
      | r2_hidden(A_18015,k5_xboole_0(B_18017,C_18016)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_15732,plain,(
    ! [A_34067,A_34068,B_34069] :
      ( r2_hidden(A_34067,k3_xboole_0(A_34068,B_34069))
      | ~ r2_hidden(A_34067,A_34068)
      | r2_hidden(A_34067,k4_xboole_0(A_34068,B_34069)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_9260])).

tff(c_15780,plain,(
    ! [A_34067] :
      ( r2_hidden(A_34067,k3_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11'))
      | ~ r2_hidden(A_34067,k2_tarski('#skF_9','#skF_10'))
      | r2_hidden(A_34067,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_15732])).

tff(c_15797,plain,(
    ! [A_34067] :
      ( r2_hidden(A_34067,k3_xboole_0('#skF_11',k2_tarski('#skF_9','#skF_10')))
      | ~ r2_hidden(A_34067,k2_tarski('#skF_9','#skF_10'))
      | r2_hidden(A_34067,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_15780])).

tff(c_15799,plain,(
    ! [A_34217] :
      ( r2_hidden(A_34217,k3_xboole_0('#skF_11',k2_tarski('#skF_9','#skF_10')))
      | ~ r2_hidden(A_34217,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8567,c_15797])).

tff(c_15862,plain,(
    ! [A_34365] :
      ( r2_hidden(A_34365,'#skF_11')
      | ~ r2_hidden(A_34365,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_15799,c_8])).

tff(c_15914,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_247,c_15862])).

tff(c_15934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8527,c_15914])).

tff(c_15935,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_8524])).

tff(c_8525,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_15936,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_8524])).

tff(c_94,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_10','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16117,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8525,c_15936,c_94])).

tff(c_44,plain,(
    ! [B_20] : r1_tarski(B_20,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_233,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(A_73,B_74) = k1_xboole_0
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_237,plain,(
    ! [B_20] : k4_xboole_0(B_20,B_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_233])).

tff(c_22,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15975,plain,(
    ! [A_34523,B_34524] : k5_xboole_0(A_34523,k3_xboole_0(A_34523,B_34524)) = k4_xboole_0(A_34523,B_34524) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_15996,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k4_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_15975])).

tff(c_15999,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_15996])).

tff(c_17076,plain,(
    ! [A_34636,C_34637,B_34638] :
      ( k3_xboole_0(k2_tarski(A_34636,C_34637),B_34638) = k2_tarski(A_34636,C_34637)
      | ~ r2_hidden(C_34637,B_34638)
      | ~ r2_hidden(A_34636,B_34638) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_17136,plain,(
    ! [A_34636,C_34637,B_34638] :
      ( k5_xboole_0(k2_tarski(A_34636,C_34637),k2_tarski(A_34636,C_34637)) = k4_xboole_0(k2_tarski(A_34636,C_34637),B_34638)
      | ~ r2_hidden(C_34637,B_34638)
      | ~ r2_hidden(A_34636,B_34638) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17076,c_50])).

tff(c_22813,plain,(
    ! [A_50639,C_50640,B_50641] :
      ( k4_xboole_0(k2_tarski(A_50639,C_50640),B_50641) = k1_xboole_0
      | ~ r2_hidden(C_50640,B_50641)
      | ~ r2_hidden(A_50639,B_50641) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15999,c_17136])).

tff(c_92,plain,
    ( k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0
    | ~ r2_hidden('#skF_10','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16403,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8525,c_15936,c_92])).

tff(c_22833,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_22813,c_16403])).

tff(c_22864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15935,c_16117,c_22833])).

tff(c_22865,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_22866,plain,(
    k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_100,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_22908,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_22866,c_100])).

tff(c_22872,plain,(
    ! [A_50794,B_50795] :
      ( k4_xboole_0(A_50794,B_50795) = k1_xboole_0
      | ~ r1_tarski(A_50794,B_50795) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22880,plain,(
    ! [B_20] : k4_xboole_0(B_20,B_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_22872])).

tff(c_22943,plain,(
    ! [A_50811,B_50812] : k5_xboole_0(A_50811,k3_xboole_0(A_50811,B_50812)) = k4_xboole_0(A_50811,B_50812) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22964,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k4_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_22943])).

tff(c_22967,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22880,c_22964])).

tff(c_24098,plain,(
    ! [A_50928,C_50929,B_50930] :
      ( k3_xboole_0(k2_tarski(A_50928,C_50929),B_50930) = k2_tarski(A_50928,C_50929)
      | ~ r2_hidden(C_50929,B_50930)
      | ~ r2_hidden(A_50928,B_50930) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24161,plain,(
    ! [A_50928,C_50929,B_50930] :
      ( k5_xboole_0(k2_tarski(A_50928,C_50929),k2_tarski(A_50928,C_50929)) = k4_xboole_0(k2_tarski(A_50928,C_50929),B_50930)
      | ~ r2_hidden(C_50929,B_50930)
      | ~ r2_hidden(A_50928,B_50930) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24098,c_50])).

tff(c_30044,plain,(
    ! [A_66935,C_66936,B_66937] :
      ( k4_xboole_0(k2_tarski(A_66935,C_66936),B_66937) = k1_xboole_0
      | ~ r2_hidden(C_66936,B_66937)
      | ~ r2_hidden(A_66935,B_66937) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22967,c_24161])).

tff(c_98,plain,
    ( k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0
    | k4_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_23111,plain,(
    k4_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22866,c_98])).

tff(c_30064,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_30044,c_23111])).

tff(c_30092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22865,c_22908,c_30064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 14:18:12 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.83/4.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.83/4.66  
% 11.83/4.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.83/4.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5
% 11.83/4.67  
% 11.83/4.67  %Foreground sorts:
% 11.83/4.67  
% 11.83/4.67  
% 11.83/4.67  %Background operators:
% 11.83/4.67  
% 11.83/4.67  
% 11.83/4.67  %Foreground operators:
% 11.83/4.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.83/4.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.83/4.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.83/4.67  tff('#skF_11', type, '#skF_11': $i).
% 11.83/4.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.83/4.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.83/4.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.83/4.67  tff('#skF_7', type, '#skF_7': $i).
% 11.83/4.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.83/4.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.83/4.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.83/4.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.83/4.67  tff('#skF_10', type, '#skF_10': $i).
% 11.83/4.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.83/4.67  tff('#skF_6', type, '#skF_6': $i).
% 11.83/4.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.83/4.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.83/4.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.83/4.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.83/4.67  tff('#skF_9', type, '#skF_9': $i).
% 11.83/4.67  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 11.83/4.67  tff('#skF_8', type, '#skF_8': $i).
% 11.83/4.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.83/4.67  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 11.83/4.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.83/4.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.83/4.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.83/4.67  
% 11.95/4.69  tff(f_113, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 11.95/4.69  tff(f_92, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 11.95/4.69  tff(f_90, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 11.95/4.69  tff(f_75, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.95/4.69  tff(f_73, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.95/4.69  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.95/4.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.95/4.69  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.95/4.69  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 11.95/4.69  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.95/4.69  tff(f_65, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.95/4.69  tff(f_69, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.95/4.69  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.95/4.69  tff(f_106, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 11.95/4.69  tff(c_96, plain, (r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_10', '#skF_11') | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.95/4.69  tff(c_265, plain, (~r2_hidden('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_96])).
% 11.95/4.69  tff(c_238, plain, (![A_75, B_76]: (k1_enumset1(A_75, A_75, B_76)=k2_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.95/4.69  tff(c_62, plain, (![E_33, B_28, C_29]: (r2_hidden(E_33, k1_enumset1(E_33, B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.95/4.69  tff(c_244, plain, (![A_75, B_76]: (r2_hidden(A_75, k2_tarski(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_238, c_62])).
% 11.95/4.69  tff(c_54, plain, (![A_26]: (r1_xboole_0(A_26, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.95/4.69  tff(c_52, plain, (![A_25]: (k3_xboole_0(A_25, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.95/4.69  tff(c_307, plain, (![A_88, B_89, C_90]: (~r1_xboole_0(A_88, B_89) | ~r2_hidden(C_90, k3_xboole_0(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.95/4.69  tff(c_319, plain, (![A_25, C_90]: (~r1_xboole_0(A_25, k1_xboole_0) | ~r2_hidden(C_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_307])).
% 11.95/4.69  tff(c_324, plain, (![C_90]: (~r2_hidden(C_90, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_319])).
% 11.95/4.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.95/4.69  tff(c_102, plain, (r2_hidden('#skF_6', '#skF_8') | k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.95/4.69  tff(c_225, plain, (k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_102])).
% 11.95/4.69  tff(c_50, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.95/4.69  tff(c_868, plain, (![A_151, C_152, B_153]: (r2_hidden(A_151, C_152) | ~r2_hidden(A_151, B_153) | r2_hidden(A_151, k5_xboole_0(B_153, C_152)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.95/4.69  tff(c_8304, plain, (![A_17484, A_17485, B_17486]: (r2_hidden(A_17484, k3_xboole_0(A_17485, B_17486)) | ~r2_hidden(A_17484, A_17485) | r2_hidden(A_17484, k4_xboole_0(A_17485, B_17486)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_868])).
% 11.95/4.69  tff(c_8364, plain, (![A_17484]: (r2_hidden(A_17484, k3_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')) | ~r2_hidden(A_17484, k2_tarski('#skF_9', '#skF_10')) | r2_hidden(A_17484, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_225, c_8304])).
% 11.95/4.69  tff(c_8385, plain, (![A_17484]: (r2_hidden(A_17484, k3_xboole_0('#skF_11', k2_tarski('#skF_9', '#skF_10'))) | ~r2_hidden(A_17484, k2_tarski('#skF_9', '#skF_10')) | r2_hidden(A_17484, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8364])).
% 11.95/4.69  tff(c_8387, plain, (![A_17634]: (r2_hidden(A_17634, k3_xboole_0('#skF_11', k2_tarski('#skF_9', '#skF_10'))) | ~r2_hidden(A_17634, k2_tarski('#skF_9', '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_324, c_8385])).
% 11.95/4.69  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.95/4.69  tff(c_8450, plain, (![A_17782]: (r2_hidden(A_17782, '#skF_11') | ~r2_hidden(A_17782, k2_tarski('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_8387, c_8])).
% 11.95/4.69  tff(c_8506, plain, (r2_hidden('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_244, c_8450])).
% 11.95/4.69  tff(c_8523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_265, c_8506])).
% 11.95/4.69  tff(c_8524, plain, (~r2_hidden('#skF_10', '#skF_11') | r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_96])).
% 11.95/4.69  tff(c_8527, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(splitLeft, [status(thm)], [c_8524])).
% 11.95/4.69  tff(c_58, plain, (![E_33, A_27, B_28]: (r2_hidden(E_33, k1_enumset1(A_27, B_28, E_33)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.95/4.69  tff(c_247, plain, (![B_76, A_75]: (r2_hidden(B_76, k2_tarski(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_238, c_58])).
% 11.95/4.69  tff(c_8550, plain, (![A_17937, B_17938, C_17939]: (~r1_xboole_0(A_17937, B_17938) | ~r2_hidden(C_17939, k3_xboole_0(A_17937, B_17938)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.95/4.69  tff(c_8562, plain, (![A_25, C_17939]: (~r1_xboole_0(A_25, k1_xboole_0) | ~r2_hidden(C_17939, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_8550])).
% 11.95/4.69  tff(c_8567, plain, (![C_17939]: (~r2_hidden(C_17939, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8562])).
% 11.95/4.69  tff(c_9260, plain, (![A_18015, C_18016, B_18017]: (r2_hidden(A_18015, C_18016) | ~r2_hidden(A_18015, B_18017) | r2_hidden(A_18015, k5_xboole_0(B_18017, C_18016)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.95/4.69  tff(c_15732, plain, (![A_34067, A_34068, B_34069]: (r2_hidden(A_34067, k3_xboole_0(A_34068, B_34069)) | ~r2_hidden(A_34067, A_34068) | r2_hidden(A_34067, k4_xboole_0(A_34068, B_34069)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_9260])).
% 11.95/4.69  tff(c_15780, plain, (![A_34067]: (r2_hidden(A_34067, k3_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')) | ~r2_hidden(A_34067, k2_tarski('#skF_9', '#skF_10')) | r2_hidden(A_34067, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_225, c_15732])).
% 11.95/4.69  tff(c_15797, plain, (![A_34067]: (r2_hidden(A_34067, k3_xboole_0('#skF_11', k2_tarski('#skF_9', '#skF_10'))) | ~r2_hidden(A_34067, k2_tarski('#skF_9', '#skF_10')) | r2_hidden(A_34067, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_15780])).
% 11.95/4.69  tff(c_15799, plain, (![A_34217]: (r2_hidden(A_34217, k3_xboole_0('#skF_11', k2_tarski('#skF_9', '#skF_10'))) | ~r2_hidden(A_34217, k2_tarski('#skF_9', '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_8567, c_15797])).
% 11.95/4.69  tff(c_15862, plain, (![A_34365]: (r2_hidden(A_34365, '#skF_11') | ~r2_hidden(A_34365, k2_tarski('#skF_9', '#skF_10')))), inference(resolution, [status(thm)], [c_15799, c_8])).
% 11.95/4.69  tff(c_15914, plain, (r2_hidden('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_247, c_15862])).
% 11.95/4.69  tff(c_15934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8527, c_15914])).
% 11.95/4.69  tff(c_15935, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_8524])).
% 11.95/4.69  tff(c_8525, plain, (r2_hidden('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_96])).
% 11.95/4.69  tff(c_15936, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_8524])).
% 11.95/4.69  tff(c_94, plain, (r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_10', '#skF_11') | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.95/4.69  tff(c_16117, plain, (r2_hidden('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8525, c_15936, c_94])).
% 11.95/4.69  tff(c_44, plain, (![B_20]: (r1_tarski(B_20, B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.95/4.69  tff(c_233, plain, (![A_73, B_74]: (k4_xboole_0(A_73, B_74)=k1_xboole_0 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.95/4.69  tff(c_237, plain, (![B_20]: (k4_xboole_0(B_20, B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_233])).
% 11.95/4.69  tff(c_22, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.95/4.69  tff(c_15975, plain, (![A_34523, B_34524]: (k5_xboole_0(A_34523, k3_xboole_0(A_34523, B_34524))=k4_xboole_0(A_34523, B_34524))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.95/4.69  tff(c_15996, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k4_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_15975])).
% 11.95/4.69  tff(c_15999, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_237, c_15996])).
% 11.95/4.69  tff(c_17076, plain, (![A_34636, C_34637, B_34638]: (k3_xboole_0(k2_tarski(A_34636, C_34637), B_34638)=k2_tarski(A_34636, C_34637) | ~r2_hidden(C_34637, B_34638) | ~r2_hidden(A_34636, B_34638))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.95/4.69  tff(c_17136, plain, (![A_34636, C_34637, B_34638]: (k5_xboole_0(k2_tarski(A_34636, C_34637), k2_tarski(A_34636, C_34637))=k4_xboole_0(k2_tarski(A_34636, C_34637), B_34638) | ~r2_hidden(C_34637, B_34638) | ~r2_hidden(A_34636, B_34638))), inference(superposition, [status(thm), theory('equality')], [c_17076, c_50])).
% 11.95/4.69  tff(c_22813, plain, (![A_50639, C_50640, B_50641]: (k4_xboole_0(k2_tarski(A_50639, C_50640), B_50641)=k1_xboole_0 | ~r2_hidden(C_50640, B_50641) | ~r2_hidden(A_50639, B_50641))), inference(demodulation, [status(thm), theory('equality')], [c_15999, c_17136])).
% 11.95/4.69  tff(c_92, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0 | ~r2_hidden('#skF_10', '#skF_11') | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.95/4.69  tff(c_16403, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8525, c_15936, c_92])).
% 11.95/4.69  tff(c_22833, plain, (~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_22813, c_16403])).
% 11.95/4.69  tff(c_22864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15935, c_16117, c_22833])).
% 11.95/4.69  tff(c_22865, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_102])).
% 11.95/4.69  tff(c_22866, plain, (k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_102])).
% 11.95/4.69  tff(c_100, plain, (r2_hidden('#skF_7', '#skF_8') | k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.95/4.69  tff(c_22908, plain, (r2_hidden('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_22866, c_100])).
% 11.95/4.69  tff(c_22872, plain, (![A_50794, B_50795]: (k4_xboole_0(A_50794, B_50795)=k1_xboole_0 | ~r1_tarski(A_50794, B_50795))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.95/4.69  tff(c_22880, plain, (![B_20]: (k4_xboole_0(B_20, B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_22872])).
% 11.95/4.69  tff(c_22943, plain, (![A_50811, B_50812]: (k5_xboole_0(A_50811, k3_xboole_0(A_50811, B_50812))=k4_xboole_0(A_50811, B_50812))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.95/4.69  tff(c_22964, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k4_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_22943])).
% 11.95/4.69  tff(c_22967, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22880, c_22964])).
% 11.95/4.69  tff(c_24098, plain, (![A_50928, C_50929, B_50930]: (k3_xboole_0(k2_tarski(A_50928, C_50929), B_50930)=k2_tarski(A_50928, C_50929) | ~r2_hidden(C_50929, B_50930) | ~r2_hidden(A_50928, B_50930))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.95/4.69  tff(c_24161, plain, (![A_50928, C_50929, B_50930]: (k5_xboole_0(k2_tarski(A_50928, C_50929), k2_tarski(A_50928, C_50929))=k4_xboole_0(k2_tarski(A_50928, C_50929), B_50930) | ~r2_hidden(C_50929, B_50930) | ~r2_hidden(A_50928, B_50930))), inference(superposition, [status(thm), theory('equality')], [c_24098, c_50])).
% 11.95/4.69  tff(c_30044, plain, (![A_66935, C_66936, B_66937]: (k4_xboole_0(k2_tarski(A_66935, C_66936), B_66937)=k1_xboole_0 | ~r2_hidden(C_66936, B_66937) | ~r2_hidden(A_66935, B_66937))), inference(demodulation, [status(thm), theory('equality')], [c_22967, c_24161])).
% 11.95/4.69  tff(c_98, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0 | k4_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.95/4.69  tff(c_23111, plain, (k4_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_22866, c_98])).
% 11.95/4.69  tff(c_30064, plain, (~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_30044, c_23111])).
% 11.95/4.69  tff(c_30092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22865, c_22908, c_30064])).
% 11.95/4.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/4.69  
% 11.95/4.69  Inference rules
% 11.95/4.69  ----------------------
% 11.95/4.69  #Ref     : 0
% 11.95/4.69  #Sup     : 5630
% 11.95/4.69  #Fact    : 72
% 11.95/4.69  #Define  : 0
% 11.95/4.69  #Split   : 7
% 11.95/4.69  #Chain   : 0
% 11.95/4.69  #Close   : 0
% 11.95/4.69  
% 11.95/4.69  Ordering : KBO
% 11.95/4.69  
% 11.95/4.69  Simplification rules
% 11.95/4.69  ----------------------
% 11.95/4.69  #Subsume      : 1817
% 11.95/4.69  #Demod        : 1461
% 11.95/4.69  #Tautology    : 1323
% 11.95/4.69  #SimpNegUnit  : 179
% 11.95/4.69  #BackRed      : 0
% 11.95/4.69  
% 11.95/4.69  #Partial instantiations: 28224
% 11.95/4.69  #Strategies tried      : 1
% 11.95/4.69  
% 11.95/4.69  Timing (in seconds)
% 11.95/4.69  ----------------------
% 11.95/4.69  Preprocessing        : 0.36
% 11.95/4.69  Parsing              : 0.19
% 11.95/4.69  CNF conversion       : 0.03
% 11.95/4.69  Main loop            : 3.52
% 11.95/4.69  Inferencing          : 1.58
% 11.95/4.69  Reduction            : 0.92
% 11.95/4.69  Demodulation         : 0.72
% 11.95/4.69  BG Simplification    : 0.14
% 11.95/4.69  Subsumption          : 0.67
% 11.95/4.69  Abstraction          : 0.17
% 11.95/4.69  MUC search           : 0.00
% 11.95/4.69  Cooper               : 0.00
% 11.95/4.69  Total                : 3.92
% 11.95/4.69  Index Insertion      : 0.00
% 11.95/4.69  Index Deletion       : 0.00
% 11.95/4.69  Index Matching       : 0.00
% 11.95/4.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
