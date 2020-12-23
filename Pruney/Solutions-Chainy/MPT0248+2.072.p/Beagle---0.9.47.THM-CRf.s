%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:14 EST 2020

% Result     : Theorem 8.52s
% Output     : CNFRefutation 8.62s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 159 expanded)
%              Number of leaves         :   43 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 295 expanded)
%              Number of equality atoms :   63 ( 216 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_111,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_80,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(k1_tarski(A_82),B_83)
      | ~ r2_hidden(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_88,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_137,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_94,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_28,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_142,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_28])).

tff(c_310,plain,(
    ! [B_121,A_122] :
      ( B_121 = A_122
      | ~ r1_tarski(B_121,A_122)
      | ~ r1_tarski(A_122,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_314,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_142,c_310])).

tff(c_322,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_314])).

tff(c_331,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_322])).

tff(c_90,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_136,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_20,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [A_77,B_78] :
      ( r1_xboole_0(k1_tarski(A_77),B_78)
      | r2_hidden(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1430,plain,(
    ! [A_188,B_189,C_190] :
      ( k1_xboole_0 = A_188
      | ~ r1_xboole_0(B_189,C_190)
      | ~ r1_tarski(A_188,C_190)
      | ~ r1_tarski(A_188,B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8771,plain,(
    ! [A_361,B_362,A_363] :
      ( k1_xboole_0 = A_361
      | ~ r1_tarski(A_361,B_362)
      | ~ r1_tarski(A_361,k1_tarski(A_363))
      | r2_hidden(A_363,B_362) ) ),
    inference(resolution,[status(thm)],[c_70,c_1430])).

tff(c_8855,plain,(
    ! [B_365,A_366] :
      ( k1_xboole_0 = B_365
      | ~ r1_tarski(B_365,k1_tarski(A_366))
      | r2_hidden(A_366,B_365) ) ),
    inference(resolution,[status(thm)],[c_20,c_8771])).

tff(c_8876,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_142,c_8855])).

tff(c_8896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_136,c_8876])).

tff(c_8897,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_8898,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_92,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_8925,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8898,c_8898,c_92])).

tff(c_8903,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8898,c_94])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_9020,plain,(
    ! [A_383,B_384] :
      ( k2_xboole_0(A_383,B_384) = B_384
      | ~ r1_tarski(A_383,B_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9032,plain,(
    ! [B_13] : k2_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_20,c_9020])).

tff(c_14,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10488,plain,(
    ! [A_489,B_490] : k5_xboole_0(k5_xboole_0(A_489,B_490),k2_xboole_0(A_489,B_490)) = k3_xboole_0(A_489,B_490) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10542,plain,(
    ! [A_25] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_25,A_25)) = k3_xboole_0(A_25,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_10488])).

tff(c_10548,plain,(
    ! [A_25] : k5_xboole_0(k1_xboole_0,A_25) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9032,c_14,c_10542])).

tff(c_10710,plain,(
    ! [A_495,B_496,C_497] : k5_xboole_0(k5_xboole_0(A_495,B_496),C_497) = k5_xboole_0(A_495,k5_xboole_0(B_496,C_497)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10790,plain,(
    ! [A_25,C_497] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_497)) = k5_xboole_0(k1_xboole_0,C_497) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_10710])).

tff(c_10806,plain,(
    ! [A_498,C_499] : k5_xboole_0(A_498,k5_xboole_0(A_498,C_499)) = C_499 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10548,c_10790])).

tff(c_10861,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10806])).

tff(c_10539,plain,(
    k5_xboole_0(k5_xboole_0('#skF_7','#skF_8'),'#skF_7') = k3_xboole_0('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_8903,c_10488])).

tff(c_10547,plain,(
    k5_xboole_0('#skF_7',k5_xboole_0('#skF_8','#skF_7')) = k3_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_10539])).

tff(c_11027,plain,(
    k3_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10861,c_10547])).

tff(c_9130,plain,(
    ! [A_392,B_393] :
      ( r1_xboole_0(k1_tarski(A_392),B_393)
      | r2_hidden(A_392,B_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_9138,plain,(
    ! [B_394] :
      ( r1_xboole_0('#skF_7',B_394)
      | r2_hidden('#skF_6',B_394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8898,c_9130])).

tff(c_8970,plain,(
    ! [A_375,B_376] :
      ( r1_tarski(k1_tarski(A_375),B_376)
      | ~ r2_hidden(A_375,B_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8973,plain,(
    ! [B_376] :
      ( r1_tarski('#skF_7',B_376)
      | ~ r2_hidden('#skF_6',B_376) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8898,c_8970])).

tff(c_9149,plain,(
    ! [B_394] :
      ( r1_tarski('#skF_7',B_394)
      | r1_xboole_0('#skF_7',B_394) ) ),
    inference(resolution,[status(thm)],[c_9138,c_8973])).

tff(c_9202,plain,(
    ! [A_400,B_401] :
      ( k3_xboole_0(A_400,B_401) = k1_xboole_0
      | ~ r1_xboole_0(A_400,B_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9245,plain,(
    ! [B_405] :
      ( k3_xboole_0('#skF_7',B_405) = k1_xboole_0
      | r1_tarski('#skF_7',B_405) ) ),
    inference(resolution,[status(thm)],[c_9149,c_9202])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9258,plain,(
    ! [B_405] :
      ( k2_xboole_0('#skF_7',B_405) = B_405
      | k3_xboole_0('#skF_7',B_405) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9245,c_22])).

tff(c_11154,plain,
    ( k2_xboole_0('#skF_7','#skF_8') = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_11027,c_9258])).

tff(c_11160,plain,
    ( '#skF_7' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8903,c_11154])).

tff(c_11162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8897,c_8925,c_11160])).

tff(c_11163,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_11391,plain,(
    ! [A_545,B_546] :
      ( r2_hidden('#skF_1'(A_545,B_546),A_545)
      | r1_tarski(A_545,B_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_11164,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_24,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_11166,plain,(
    ! [A_16] : r1_xboole_0(A_16,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11164,c_24])).

tff(c_11245,plain,(
    ! [A_518,B_519] :
      ( ~ r2_hidden(A_518,B_519)
      | ~ r1_xboole_0(k1_tarski(A_518),B_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_11250,plain,(
    ! [A_518] : ~ r2_hidden(A_518,'#skF_7') ),
    inference(resolution,[status(thm)],[c_11166,c_11245])).

tff(c_11404,plain,(
    ! [B_547] : r1_tarski('#skF_7',B_547) ),
    inference(resolution,[status(thm)],[c_11391,c_11250])).

tff(c_11408,plain,(
    ! [B_547] : k2_xboole_0('#skF_7',B_547) = B_547 ),
    inference(resolution,[status(thm)],[c_11404,c_22])).

tff(c_11426,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11408,c_94])).

tff(c_11428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11163,c_11426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:05:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.52/2.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.62/2.92  
% 8.62/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.62/2.93  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 8.62/2.93  
% 8.62/2.93  %Foreground sorts:
% 8.62/2.93  
% 8.62/2.93  
% 8.62/2.93  %Background operators:
% 8.62/2.93  
% 8.62/2.93  
% 8.62/2.93  %Foreground operators:
% 8.62/2.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.62/2.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.62/2.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.62/2.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.62/2.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.62/2.93  tff('#skF_7', type, '#skF_7': $i).
% 8.62/2.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.62/2.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.62/2.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.62/2.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.62/2.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.62/2.93  tff('#skF_6', type, '#skF_6': $i).
% 8.62/2.93  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.62/2.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.62/2.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.62/2.93  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.62/2.93  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.62/2.93  tff('#skF_8', type, '#skF_8': $i).
% 8.62/2.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.62/2.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.62/2.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.62/2.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.62/2.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.62/2.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.62/2.93  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.62/2.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.62/2.93  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.62/2.93  
% 8.62/2.94  tff(f_111, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 8.62/2.94  tff(f_136, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 8.62/2.94  tff(f_62, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.62/2.94  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.62/2.94  tff(f_102, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 8.62/2.94  tff(f_60, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 8.62/2.94  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.62/2.94  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.62/2.94  tff(f_40, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.62/2.94  tff(f_66, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.62/2.94  tff(f_68, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.62/2.94  tff(f_64, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.62/2.94  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.62/2.94  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.62/2.94  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 8.62/2.94  tff(f_97, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 8.62/2.94  tff(c_80, plain, (![A_82, B_83]: (r1_tarski(k1_tarski(A_82), B_83) | ~r2_hidden(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.62/2.94  tff(c_88, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.62/2.94  tff(c_137, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_88])).
% 8.62/2.94  tff(c_94, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.62/2.94  tff(c_28, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.62/2.94  tff(c_142, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_28])).
% 8.62/2.94  tff(c_310, plain, (![B_121, A_122]: (B_121=A_122 | ~r1_tarski(B_121, A_122) | ~r1_tarski(A_122, B_121))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.62/2.94  tff(c_314, plain, (k1_tarski('#skF_6')='#skF_7' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_142, c_310])).
% 8.62/2.94  tff(c_322, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_137, c_314])).
% 8.62/2.94  tff(c_331, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_80, c_322])).
% 8.62/2.94  tff(c_90, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.62/2.94  tff(c_136, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_90])).
% 8.62/2.94  tff(c_20, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.62/2.94  tff(c_70, plain, (![A_77, B_78]: (r1_xboole_0(k1_tarski(A_77), B_78) | r2_hidden(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.62/2.94  tff(c_1430, plain, (![A_188, B_189, C_190]: (k1_xboole_0=A_188 | ~r1_xboole_0(B_189, C_190) | ~r1_tarski(A_188, C_190) | ~r1_tarski(A_188, B_189))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.62/2.94  tff(c_8771, plain, (![A_361, B_362, A_363]: (k1_xboole_0=A_361 | ~r1_tarski(A_361, B_362) | ~r1_tarski(A_361, k1_tarski(A_363)) | r2_hidden(A_363, B_362))), inference(resolution, [status(thm)], [c_70, c_1430])).
% 8.62/2.94  tff(c_8855, plain, (![B_365, A_366]: (k1_xboole_0=B_365 | ~r1_tarski(B_365, k1_tarski(A_366)) | r2_hidden(A_366, B_365))), inference(resolution, [status(thm)], [c_20, c_8771])).
% 8.62/2.94  tff(c_8876, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_142, c_8855])).
% 8.62/2.94  tff(c_8896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_331, c_136, c_8876])).
% 8.62/2.94  tff(c_8897, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_88])).
% 8.62/2.94  tff(c_8898, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_88])).
% 8.62/2.94  tff(c_92, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.62/2.94  tff(c_8925, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8898, c_8898, c_92])).
% 8.62/2.94  tff(c_8903, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8898, c_94])).
% 8.62/2.94  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.62/2.94  tff(c_9020, plain, (![A_383, B_384]: (k2_xboole_0(A_383, B_384)=B_384 | ~r1_tarski(A_383, B_384))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.62/2.94  tff(c_9032, plain, (![B_13]: (k2_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_20, c_9020])).
% 8.62/2.94  tff(c_14, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.62/2.94  tff(c_32, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.62/2.94  tff(c_10488, plain, (![A_489, B_490]: (k5_xboole_0(k5_xboole_0(A_489, B_490), k2_xboole_0(A_489, B_490))=k3_xboole_0(A_489, B_490))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.62/2.94  tff(c_10542, plain, (![A_25]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_25, A_25))=k3_xboole_0(A_25, A_25))), inference(superposition, [status(thm), theory('equality')], [c_32, c_10488])).
% 8.62/2.94  tff(c_10548, plain, (![A_25]: (k5_xboole_0(k1_xboole_0, A_25)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_9032, c_14, c_10542])).
% 8.62/2.94  tff(c_10710, plain, (![A_495, B_496, C_497]: (k5_xboole_0(k5_xboole_0(A_495, B_496), C_497)=k5_xboole_0(A_495, k5_xboole_0(B_496, C_497)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.62/2.94  tff(c_10790, plain, (![A_25, C_497]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_497))=k5_xboole_0(k1_xboole_0, C_497))), inference(superposition, [status(thm), theory('equality')], [c_32, c_10710])).
% 8.62/2.94  tff(c_10806, plain, (![A_498, C_499]: (k5_xboole_0(A_498, k5_xboole_0(A_498, C_499))=C_499)), inference(demodulation, [status(thm), theory('equality')], [c_10548, c_10790])).
% 8.62/2.94  tff(c_10861, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_10806])).
% 8.62/2.94  tff(c_10539, plain, (k5_xboole_0(k5_xboole_0('#skF_7', '#skF_8'), '#skF_7')=k3_xboole_0('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_8903, c_10488])).
% 8.62/2.94  tff(c_10547, plain, (k5_xboole_0('#skF_7', k5_xboole_0('#skF_8', '#skF_7'))=k3_xboole_0('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_10539])).
% 8.62/2.94  tff(c_11027, plain, (k3_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10861, c_10547])).
% 8.62/2.94  tff(c_9130, plain, (![A_392, B_393]: (r1_xboole_0(k1_tarski(A_392), B_393) | r2_hidden(A_392, B_393))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.62/2.94  tff(c_9138, plain, (![B_394]: (r1_xboole_0('#skF_7', B_394) | r2_hidden('#skF_6', B_394))), inference(superposition, [status(thm), theory('equality')], [c_8898, c_9130])).
% 8.62/2.94  tff(c_8970, plain, (![A_375, B_376]: (r1_tarski(k1_tarski(A_375), B_376) | ~r2_hidden(A_375, B_376))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.62/2.94  tff(c_8973, plain, (![B_376]: (r1_tarski('#skF_7', B_376) | ~r2_hidden('#skF_6', B_376))), inference(superposition, [status(thm), theory('equality')], [c_8898, c_8970])).
% 8.62/2.94  tff(c_9149, plain, (![B_394]: (r1_tarski('#skF_7', B_394) | r1_xboole_0('#skF_7', B_394))), inference(resolution, [status(thm)], [c_9138, c_8973])).
% 8.62/2.94  tff(c_9202, plain, (![A_400, B_401]: (k3_xboole_0(A_400, B_401)=k1_xboole_0 | ~r1_xboole_0(A_400, B_401))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.62/2.94  tff(c_9245, plain, (![B_405]: (k3_xboole_0('#skF_7', B_405)=k1_xboole_0 | r1_tarski('#skF_7', B_405))), inference(resolution, [status(thm)], [c_9149, c_9202])).
% 8.62/2.94  tff(c_22, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.62/2.94  tff(c_9258, plain, (![B_405]: (k2_xboole_0('#skF_7', B_405)=B_405 | k3_xboole_0('#skF_7', B_405)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9245, c_22])).
% 8.62/2.94  tff(c_11154, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_11027, c_9258])).
% 8.62/2.94  tff(c_11160, plain, ('#skF_7'='#skF_8' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8903, c_11154])).
% 8.62/2.94  tff(c_11162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8897, c_8925, c_11160])).
% 8.62/2.94  tff(c_11163, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_90])).
% 8.62/2.94  tff(c_11391, plain, (![A_545, B_546]: (r2_hidden('#skF_1'(A_545, B_546), A_545) | r1_tarski(A_545, B_546))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.62/2.94  tff(c_11164, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_90])).
% 8.62/2.94  tff(c_24, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.62/2.94  tff(c_11166, plain, (![A_16]: (r1_xboole_0(A_16, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_11164, c_24])).
% 8.62/2.94  tff(c_11245, plain, (![A_518, B_519]: (~r2_hidden(A_518, B_519) | ~r1_xboole_0(k1_tarski(A_518), B_519))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.62/2.94  tff(c_11250, plain, (![A_518]: (~r2_hidden(A_518, '#skF_7'))), inference(resolution, [status(thm)], [c_11166, c_11245])).
% 8.62/2.94  tff(c_11404, plain, (![B_547]: (r1_tarski('#skF_7', B_547))), inference(resolution, [status(thm)], [c_11391, c_11250])).
% 8.62/2.94  tff(c_11408, plain, (![B_547]: (k2_xboole_0('#skF_7', B_547)=B_547)), inference(resolution, [status(thm)], [c_11404, c_22])).
% 8.62/2.94  tff(c_11426, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11408, c_94])).
% 8.62/2.94  tff(c_11428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11163, c_11426])).
% 8.62/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.62/2.94  
% 8.62/2.94  Inference rules
% 8.62/2.94  ----------------------
% 8.62/2.94  #Ref     : 0
% 8.62/2.94  #Sup     : 2815
% 8.62/2.94  #Fact    : 0
% 8.62/2.94  #Define  : 0
% 8.62/2.94  #Split   : 6
% 8.62/2.94  #Chain   : 0
% 8.62/2.94  #Close   : 0
% 8.62/2.94  
% 8.62/2.94  Ordering : KBO
% 8.62/2.94  
% 8.62/2.94  Simplification rules
% 8.62/2.94  ----------------------
% 8.62/2.94  #Subsume      : 257
% 8.62/2.94  #Demod        : 2413
% 8.62/2.94  #Tautology    : 1313
% 8.62/2.94  #SimpNegUnit  : 41
% 8.62/2.94  #BackRed      : 15
% 8.62/2.94  
% 8.62/2.94  #Partial instantiations: 0
% 8.62/2.94  #Strategies tried      : 1
% 8.62/2.94  
% 8.62/2.94  Timing (in seconds)
% 8.62/2.94  ----------------------
% 8.62/2.94  Preprocessing        : 0.37
% 8.62/2.94  Parsing              : 0.19
% 8.62/2.94  CNF conversion       : 0.03
% 8.62/2.94  Main loop            : 1.81
% 8.62/2.94  Inferencing          : 0.44
% 8.62/2.94  Reduction            : 0.89
% 8.62/2.94  Demodulation         : 0.75
% 8.62/2.94  BG Simplification    : 0.06
% 8.62/2.95  Subsumption          : 0.31
% 8.62/2.95  Abstraction          : 0.07
% 8.62/2.95  MUC search           : 0.00
% 8.62/2.95  Cooper               : 0.00
% 8.62/2.95  Total                : 2.22
% 8.62/2.95  Index Insertion      : 0.00
% 8.62/2.95  Index Deletion       : 0.00
% 8.62/2.95  Index Matching       : 0.00
% 8.62/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
