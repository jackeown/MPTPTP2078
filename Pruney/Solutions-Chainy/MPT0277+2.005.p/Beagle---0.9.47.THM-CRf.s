%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:20 EST 2020

% Result     : Theorem 5.82s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :  262 ( 945 expanded)
%              Number of leaves         :   37 ( 281 expanded)
%              Depth                    :   10
%              Number of atoms          :  360 (2057 expanded)
%              Number of equality atoms :  295 (1970 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_7701,plain,(
    ! [A_479,B_480] : k1_enumset1(A_479,A_479,B_480) = k2_tarski(A_479,B_480) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [E_19,A_13,B_14] : r2_hidden(E_19,k1_enumset1(A_13,B_14,E_19)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7707,plain,(
    ! [B_480,A_479] : r2_hidden(B_480,k2_tarski(A_479,B_480)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7701,c_18])).

tff(c_7774,plain,(
    ! [A_491,B_492] : k4_xboole_0(A_491,k4_xboole_0(A_491,B_492)) = k3_xboole_0(A_491,B_492) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_165,plain,(
    ! [A_60,B_61] : k1_enumset1(A_60,A_60,B_61) = k2_tarski(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_171,plain,(
    ! [B_61,A_60] : r2_hidden(B_61,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_18])).

tff(c_6490,plain,(
    ! [A_389,B_390] : k4_xboole_0(A_389,k4_xboole_0(A_389,B_390)) = k3_xboole_0(A_389,B_390) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6535,plain,(
    ! [B_391] : k3_xboole_0(k1_xboole_0,B_391) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6490,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6540,plain,(
    ! [B_391] : k3_xboole_0(B_391,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6535,c_2])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6451,plain,(
    ! [A_386,B_387] : k5_xboole_0(A_386,k4_xboole_0(B_387,A_386)) = k2_xboole_0(A_386,B_387) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6472,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k2_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6451])).

tff(c_6475,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6472])).

tff(c_6591,plain,(
    ! [A_393,B_394] : k5_xboole_0(A_393,k3_xboole_0(A_393,B_394)) = k4_xboole_0(A_393,B_394) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6600,plain,(
    ! [B_391] : k5_xboole_0(B_391,k1_xboole_0) = k4_xboole_0(B_391,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6540,c_6591])).

tff(c_6617,plain,(
    ! [B_395] : k4_xboole_0(B_395,k1_xboole_0) = B_395 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6475,c_6600])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6623,plain,(
    ! [B_395] : k4_xboole_0(B_395,B_395) = k3_xboole_0(B_395,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6617,c_10])).

tff(c_6642,plain,(
    ! [B_395] : k4_xboole_0(B_395,B_395) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6540,c_6623])).

tff(c_5297,plain,(
    ! [A_310,B_311] : k4_xboole_0(A_310,k4_xboole_0(A_310,B_311)) = k3_xboole_0(A_310,B_311) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5342,plain,(
    ! [B_312] : k3_xboole_0(k1_xboole_0,B_312) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5297,c_12])).

tff(c_5360,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5342])).

tff(c_218,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_230,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = k2_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_218])).

tff(c_233,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_230])).

tff(c_5384,plain,(
    ! [A_315] : k3_xboole_0(A_315,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5342])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5389,plain,(
    ! [A_315] : k5_xboole_0(A_315,k1_xboole_0) = k4_xboole_0(A_315,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5384,c_4])).

tff(c_5424,plain,(
    ! [A_316] : k4_xboole_0(A_316,k1_xboole_0) = A_316 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_5389])).

tff(c_5430,plain,(
    ! [A_316] : k4_xboole_0(A_316,A_316) = k3_xboole_0(A_316,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5424,c_10])).

tff(c_5449,plain,(
    ! [A_316] : k4_xboole_0(A_316,A_316) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5360,c_5430])).

tff(c_78,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_155,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_74,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_267,plain,(
    k1_tarski('#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_70,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k1_tarski('#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_188,plain,(
    k1_tarski('#skF_8') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_66,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k2_tarski('#skF_7','#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_396,plain,(
    k2_tarski('#skF_7','#skF_8') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_283,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_322,plain,(
    ! [B_80] : k3_xboole_0(k1_xboole_0,B_80) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_12])).

tff(c_358,plain,(
    ! [A_84] : k3_xboole_0(A_84,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_322])).

tff(c_366,plain,(
    ! [A_84] : k5_xboole_0(A_84,k1_xboole_0) = k4_xboole_0(A_84,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_4])).

tff(c_388,plain,(
    ! [A_84] : k4_xboole_0(A_84,k1_xboole_0) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_366])).

tff(c_343,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_322])).

tff(c_399,plain,(
    ! [A_85] : k4_xboole_0(A_85,k1_xboole_0) = A_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_366])).

tff(c_405,plain,(
    ! [A_85] : k4_xboole_0(A_85,A_85) = k3_xboole_0(A_85,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_10])).

tff(c_424,plain,(
    ! [A_85] : k4_xboole_0(A_85,A_85) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_405])).

tff(c_84,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1665,plain,(
    k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_1669,plain,(
    k3_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k4_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1665,c_10])).

tff(c_1678,plain,(
    k3_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_1669])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_617,plain,(
    ! [A_94,B_95] : r1_tarski(k3_xboole_0(A_94,B_95),A_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_8])).

tff(c_629,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_617])).

tff(c_1691,plain,(
    r1_tarski('#skF_6',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1678,c_629])).

tff(c_1734,plain,(
    ! [B_148,C_149,A_150] :
      ( k2_tarski(B_148,C_149) = A_150
      | k1_tarski(C_149) = A_150
      | k1_tarski(B_148) = A_150
      | k1_xboole_0 = A_150
      | ~ r1_tarski(A_150,k2_tarski(B_148,C_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1737,plain,
    ( k2_tarski('#skF_7','#skF_8') = '#skF_6'
    | k1_tarski('#skF_8') = '#skF_6'
    | k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1691,c_1734])).

tff(c_1774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_267,c_188,c_396,c_1737])).

tff(c_1775,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1804,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1775])).

tff(c_82,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_579,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_1805,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1804,c_579])).

tff(c_1808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_1805])).

tff(c_1809,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1775])).

tff(c_1811,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1809])).

tff(c_1832,plain,(
    ! [A_10] : k4_xboole_0('#skF_3',A_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1811,c_1811,c_12])).

tff(c_1820,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1811,c_579])).

tff(c_1861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1832,c_1820])).

tff(c_1862,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1809])).

tff(c_1864,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1862])).

tff(c_58,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(k1_tarski(A_31),B_32) = k1_tarski(A_31)
      | k4_xboole_0(k1_tarski(A_31),B_32) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_953,plain,(
    ! [A_109,C_110,B_111] :
      ( ~ r2_hidden(A_109,C_110)
      | k4_xboole_0(k2_tarski(A_109,B_111),C_110) != k2_tarski(A_109,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_968,plain,(
    ! [A_20,C_110] :
      ( ~ r2_hidden(A_20,C_110)
      | k4_xboole_0(k1_tarski(A_20),C_110) != k2_tarski(A_20,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_953])).

tff(c_998,plain,(
    ! [A_119,C_120] :
      ( ~ r2_hidden(A_119,C_120)
      | k4_xboole_0(k1_tarski(A_119),C_120) != k1_tarski(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_968])).

tff(c_1019,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden(A_31,B_32)
      | k4_xboole_0(k1_tarski(A_31),B_32) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_998])).

tff(c_2165,plain,(
    ! [B_177] :
      ( ~ r2_hidden('#skF_5',B_177)
      | k4_xboole_0('#skF_3',B_177) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1864,c_1019])).

tff(c_2199,plain,(
    ! [A_60] : k4_xboole_0('#skF_3',k2_tarski(A_60,'#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_171,c_2165])).

tff(c_2243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2199,c_579])).

tff(c_2244,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1862])).

tff(c_56,plain,(
    ! [A_29,B_30] : k4_xboole_0(k1_tarski(A_29),k2_tarski(A_29,B_30)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2284,plain,(
    ! [B_30] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',B_30)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2244,c_56])).

tff(c_2387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2284,c_579])).

tff(c_2388,plain,(
    k4_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_2471,plain,(
    k3_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = k4_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2388,c_10])).

tff(c_2480,plain,(
    k3_xboole_0('#skF_6',k2_tarski('#skF_7','#skF_8')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_2471])).

tff(c_2427,plain,(
    ! [A_186,B_187] : r1_tarski(k3_xboole_0(A_186,B_187),A_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_8])).

tff(c_2439,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2427])).

tff(c_2503,plain,(
    r1_tarski('#skF_6',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2480,c_2439])).

tff(c_3775,plain,(
    ! [B_240,C_241,A_242] :
      ( k2_tarski(B_240,C_241) = A_242
      | k1_tarski(C_241) = A_242
      | k1_tarski(B_240) = A_242
      | k1_xboole_0 = A_242
      | ~ r1_tarski(A_242,k2_tarski(B_240,C_241)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3785,plain,
    ( k2_tarski('#skF_7','#skF_8') = '#skF_6'
    | k1_tarski('#skF_8') = '#skF_6'
    | k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2503,c_3775])).

tff(c_3822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_267,c_188,c_396,c_3785])).

tff(c_3823,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_3859,plain,(
    ! [A_243] : k4_xboole_0(A_243,k1_xboole_0) = A_243 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_366])).

tff(c_3865,plain,(
    ! [A_243] : k4_xboole_0(A_243,A_243) = k3_xboole_0(A_243,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3859,c_10])).

tff(c_3884,plain,(
    ! [A_243] : k4_xboole_0(A_243,A_243) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_3865])).

tff(c_3824,plain,(
    k2_tarski('#skF_7','#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_68,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_tarski('#skF_7','#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4359,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_68])).

tff(c_4360,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4359])).

tff(c_4378,plain,(
    ! [A_10] : k4_xboole_0('#skF_3',A_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4360,c_4360,c_12])).

tff(c_3855,plain,
    ( k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0
    | k4_xboole_0('#skF_6','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_82])).

tff(c_3856,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3855])).

tff(c_4371,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4360,c_3856])).

tff(c_4554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4378,c_4371])).

tff(c_4555,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4359])).

tff(c_4780,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4555])).

tff(c_4781,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4780,c_3856])).

tff(c_4784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3884,c_4781])).

tff(c_4785,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4555])).

tff(c_4787,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4785])).

tff(c_4808,plain,(
    ! [B_30] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',B_30)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4787,c_56])).

tff(c_4838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4808,c_3856])).

tff(c_4839,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4785])).

tff(c_4129,plain,(
    ! [A_255,C_256,B_257] :
      ( ~ r2_hidden(A_255,C_256)
      | k4_xboole_0(k2_tarski(A_255,B_257),C_256) != k2_tarski(A_255,B_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4147,plain,(
    ! [A_20,C_256] :
      ( ~ r2_hidden(A_20,C_256)
      | k4_xboole_0(k1_tarski(A_20),C_256) != k2_tarski(A_20,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4129])).

tff(c_4564,plain,(
    ! [A_283,C_284] :
      ( ~ r2_hidden(A_283,C_284)
      | k4_xboole_0(k1_tarski(A_283),C_284) != k1_tarski(A_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4147])).

tff(c_4586,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden(A_31,B_32)
      | k4_xboole_0(k1_tarski(A_31),B_32) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_4564])).

tff(c_4987,plain,(
    ! [B_299] :
      ( ~ r2_hidden('#skF_5',B_299)
      | k4_xboole_0('#skF_3',B_299) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4839,c_4586])).

tff(c_5021,plain,(
    ! [A_60] : k4_xboole_0('#skF_3',k2_tarski(A_60,'#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_171,c_4987])).

tff(c_5028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5021,c_3856])).

tff(c_5030,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3855])).

tff(c_5199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3823,c_5030])).

tff(c_5201,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_76,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5543,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5201,c_76])).

tff(c_5544,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5543])).

tff(c_5556,plain,(
    ! [A_10] : k4_xboole_0('#skF_3',A_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5544,c_5544,c_12])).

tff(c_5200,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_5551,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5544,c_5200])).

tff(c_5599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5556,c_5551])).

tff(c_5600,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5543])).

tff(c_5732,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5600])).

tff(c_5733,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5732,c_5200])).

tff(c_5736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5449,c_5733])).

tff(c_5737,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5600])).

tff(c_5739,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5737])).

tff(c_5744,plain,(
    ! [B_30] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',B_30)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5739,c_56])).

tff(c_5771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5744,c_5200])).

tff(c_5772,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5737])).

tff(c_5905,plain,(
    ! [B_342,C_343,A_344] :
      ( ~ r2_hidden(B_342,C_343)
      | k4_xboole_0(k2_tarski(A_344,B_342),C_343) != k2_tarski(A_344,B_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5920,plain,(
    ! [A_20,C_343] :
      ( ~ r2_hidden(A_20,C_343)
      | k4_xboole_0(k1_tarski(A_20),C_343) != k2_tarski(A_20,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5905])).

tff(c_5992,plain,(
    ! [A_352,C_353] :
      ( ~ r2_hidden(A_352,C_353)
      | k4_xboole_0(k1_tarski(A_352),C_353) != k1_tarski(A_352) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5920])).

tff(c_5995,plain,(
    ! [C_353] :
      ( ~ r2_hidden('#skF_5',C_353)
      | k4_xboole_0('#skF_3',C_353) != k1_tarski('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5772,c_5992])).

tff(c_6021,plain,(
    ! [C_354] :
      ( ~ r2_hidden('#skF_5',C_354)
      | k4_xboole_0('#skF_3',C_354) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5772,c_5995])).

tff(c_6055,plain,(
    ! [A_60] : k4_xboole_0('#skF_3',k2_tarski(A_60,'#skF_5')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_171,c_6021])).

tff(c_6173,plain,(
    ! [A_373,B_374] :
      ( k4_xboole_0(k1_tarski(A_373),B_374) = k1_tarski(A_373)
      | k4_xboole_0(k1_tarski(A_373),B_374) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6210,plain,(
    ! [B_374] :
      ( k4_xboole_0('#skF_3',B_374) = k1_tarski('#skF_5')
      | k4_xboole_0(k1_tarski('#skF_5'),B_374) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5772,c_6173])).

tff(c_6256,plain,(
    ! [B_375] :
      ( k4_xboole_0('#skF_3',B_375) = '#skF_3'
      | k4_xboole_0('#skF_3',B_375) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5772,c_5772,c_6210])).

tff(c_6292,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6256,c_5200])).

tff(c_6335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6055,c_6292])).

tff(c_6337,plain,(
    k1_tarski('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_72,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_8') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6792,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6337,c_72])).

tff(c_6793,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6792])).

tff(c_6806,plain,(
    ! [A_10] : k4_xboole_0('#skF_3',A_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6793,c_6793,c_12])).

tff(c_6336,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_6803,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6793,c_6336])).

tff(c_6859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6806,c_6803])).

tff(c_6860,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6792])).

tff(c_7013,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6860])).

tff(c_7014,plain,(
    k4_xboole_0('#skF_3','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7013,c_6336])).

tff(c_7017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6642,c_7014])).

tff(c_7018,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6860])).

tff(c_7020,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7018])).

tff(c_7026,plain,(
    ! [B_30] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',B_30)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7020,c_56])).

tff(c_7126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7026,c_6336])).

tff(c_7127,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7018])).

tff(c_7210,plain,(
    ! [A_424,C_425,B_426] :
      ( ~ r2_hidden(A_424,C_425)
      | k4_xboole_0(k2_tarski(A_424,B_426),C_425) != k2_tarski(A_424,B_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7225,plain,(
    ! [A_20,C_425] :
      ( ~ r2_hidden(A_20,C_425)
      | k4_xboole_0(k1_tarski(A_20),C_425) != k2_tarski(A_20,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_7210])).

tff(c_7255,plain,(
    ! [A_432,C_433] :
      ( ~ r2_hidden(A_432,C_433)
      | k4_xboole_0(k1_tarski(A_432),C_433) != k1_tarski(A_432) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7225])).

tff(c_7258,plain,(
    ! [C_433] :
      ( ~ r2_hidden('#skF_5',C_433)
      | k4_xboole_0('#skF_3',C_433) != k1_tarski('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7127,c_7255])).

tff(c_7284,plain,(
    ! [C_434] :
      ( ~ r2_hidden('#skF_5',C_434)
      | k4_xboole_0('#skF_3',C_434) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7127,c_7258])).

tff(c_7318,plain,(
    ! [A_60] : k4_xboole_0('#skF_3',k2_tarski(A_60,'#skF_5')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_171,c_7284])).

tff(c_7452,plain,(
    ! [A_454,B_455] :
      ( k4_xboole_0(k1_tarski(A_454),B_455) = k1_tarski(A_454)
      | k4_xboole_0(k1_tarski(A_454),B_455) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7489,plain,(
    ! [B_455] :
      ( k4_xboole_0('#skF_3',B_455) = k1_tarski('#skF_5')
      | k4_xboole_0(k1_tarski('#skF_5'),B_455) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7127,c_7452])).

tff(c_7535,plain,(
    ! [B_456] :
      ( k4_xboole_0('#skF_3',B_456) = '#skF_3'
      | k4_xboole_0('#skF_3',B_456) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7127,c_7127,c_7489])).

tff(c_7574,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7535,c_6336])).

tff(c_7615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7318,c_7574])).

tff(c_7617,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_7622,plain,(
    ! [A_10] : k4_xboole_0('#skF_6',A_10) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7617,c_7617,c_12])).

tff(c_7813,plain,(
    ! [B_493] : k3_xboole_0('#skF_6',B_493) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_7774,c_7622])).

tff(c_7821,plain,(
    ! [B_493] : k3_xboole_0(B_493,'#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_7813,c_2])).

tff(c_7621,plain,(
    ! [A_5] : k2_xboole_0(A_5,'#skF_6') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7617,c_6])).

tff(c_7731,plain,(
    ! [A_486,B_487] : k5_xboole_0(A_486,k4_xboole_0(B_487,A_486)) = k2_xboole_0(A_486,B_487) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7746,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_6') = k2_xboole_0(A_10,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7622,c_7731])).

tff(c_7749,plain,(
    ! [A_10] : k5_xboole_0(A_10,'#skF_6') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7621,c_7746])).

tff(c_7841,plain,(
    ! [B_494] : k3_xboole_0(B_494,'#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_7813,c_2])).

tff(c_7849,plain,(
    ! [B_494] : k5_xboole_0(B_494,'#skF_6') = k4_xboole_0(B_494,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7841,c_4])).

tff(c_7881,plain,(
    ! [B_495] : k4_xboole_0(B_495,'#skF_6') = B_495 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7749,c_7849])).

tff(c_7887,plain,(
    ! [B_495] : k4_xboole_0(B_495,B_495) = k3_xboole_0(B_495,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7881,c_10])).

tff(c_7906,plain,(
    ! [B_495] : k4_xboole_0(B_495,B_495) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7821,c_7887])).

tff(c_80,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7964,plain,
    ( k2_tarski('#skF_4','#skF_5') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3'
    | '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7617,c_7617,c_80])).

tff(c_7965,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7964])).

tff(c_7975,plain,(
    ! [A_10] : k4_xboole_0('#skF_3',A_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7965,c_7965,c_7622])).

tff(c_7616,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_7660,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7617,c_7616])).

tff(c_7973,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7965,c_7660])).

tff(c_8100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7975,c_7973])).

tff(c_8101,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | k1_tarski('#skF_5') = '#skF_3'
    | k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7964])).

tff(c_8264,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8101])).

tff(c_8265,plain,(
    k4_xboole_0('#skF_3','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8264,c_7660])).

tff(c_8268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7906,c_8265])).

tff(c_8269,plain,
    ( k1_tarski('#skF_5') = '#skF_3'
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8101])).

tff(c_8271,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8269])).

tff(c_7666,plain,(
    ! [A_29,B_30] : k4_xboole_0(k1_tarski(A_29),k2_tarski(A_29,B_30)) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7617,c_56])).

tff(c_8280,plain,(
    ! [B_30] : k4_xboole_0('#skF_3',k2_tarski('#skF_4',B_30)) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_8271,c_7666])).

tff(c_8304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8280,c_7660])).

tff(c_8305,plain,(
    k1_tarski('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8269])).

tff(c_8438,plain,(
    ! [A_524,C_525,B_526] :
      ( ~ r2_hidden(A_524,C_525)
      | k4_xboole_0(k2_tarski(A_524,B_526),C_525) != k2_tarski(A_524,B_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8453,plain,(
    ! [A_20,C_525] :
      ( ~ r2_hidden(A_20,C_525)
      | k4_xboole_0(k1_tarski(A_20),C_525) != k2_tarski(A_20,A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_8438])).

tff(c_8481,plain,(
    ! [A_532,C_533] :
      ( ~ r2_hidden(A_532,C_533)
      | k4_xboole_0(k1_tarski(A_532),C_533) != k1_tarski(A_532) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8453])).

tff(c_8484,plain,(
    ! [C_533] :
      ( ~ r2_hidden('#skF_5',C_533)
      | k4_xboole_0('#skF_3',C_533) != k1_tarski('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8305,c_8481])).

tff(c_8506,plain,(
    ! [C_534] :
      ( ~ r2_hidden('#skF_5',C_534)
      | k4_xboole_0('#skF_3',C_534) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8305,c_8484])).

tff(c_8540,plain,(
    ! [A_479] : k4_xboole_0('#skF_3',k2_tarski(A_479,'#skF_5')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_7707,c_8506])).

tff(c_8563,plain,(
    ! [A_538,B_539] :
      ( k4_xboole_0(k1_tarski(A_538),B_539) = k1_tarski(A_538)
      | k4_xboole_0(k1_tarski(A_538),B_539) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7617,c_58])).

tff(c_8600,plain,(
    ! [B_539] :
      ( k4_xboole_0('#skF_3',B_539) = k1_tarski('#skF_5')
      | k4_xboole_0(k1_tarski('#skF_5'),B_539) = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8305,c_8563])).

tff(c_8654,plain,(
    ! [B_544] :
      ( k4_xboole_0('#skF_3',B_544) = '#skF_3'
      | k4_xboole_0('#skF_3',B_544) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8305,c_8305,c_8600])).

tff(c_8693,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_4','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8654,c_7660])).

tff(c_8734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8540,c_8693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:20:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.82/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.24  
% 6.06/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.24  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 6.06/2.24  
% 6.06/2.24  %Foreground sorts:
% 6.06/2.24  
% 6.06/2.24  
% 6.06/2.24  %Background operators:
% 6.06/2.24  
% 6.06/2.24  
% 6.06/2.24  %Foreground operators:
% 6.06/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.06/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.06/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.06/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.06/2.24  tff('#skF_7', type, '#skF_7': $i).
% 6.06/2.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.06/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.06/2.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.06/2.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.06/2.24  tff('#skF_5', type, '#skF_5': $i).
% 6.06/2.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.06/2.24  tff('#skF_6', type, '#skF_6': $i).
% 6.06/2.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.06/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.06/2.24  tff('#skF_8', type, '#skF_8': $i).
% 6.06/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.24  tff('#skF_4', type, '#skF_4': $i).
% 6.06/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.06/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.06/2.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.06/2.24  
% 6.06/2.27  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.06/2.27  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.06/2.27  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.06/2.27  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 6.06/2.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.06/2.27  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.06/2.27  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.06/2.27  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.06/2.27  tff(f_105, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 6.06/2.27  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.06/2.27  tff(f_75, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 6.06/2.27  tff(f_81, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 6.06/2.27  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.06/2.27  tff(f_89, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 6.06/2.27  tff(f_77, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 6.06/2.27  tff(c_7701, plain, (![A_479, B_480]: (k1_enumset1(A_479, A_479, B_480)=k2_tarski(A_479, B_480))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.06/2.27  tff(c_18, plain, (![E_19, A_13, B_14]: (r2_hidden(E_19, k1_enumset1(A_13, B_14, E_19)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.06/2.27  tff(c_7707, plain, (![B_480, A_479]: (r2_hidden(B_480, k2_tarski(A_479, B_480)))), inference(superposition, [status(thm), theory('equality')], [c_7701, c_18])).
% 6.06/2.27  tff(c_7774, plain, (![A_491, B_492]: (k4_xboole_0(A_491, k4_xboole_0(A_491, B_492))=k3_xboole_0(A_491, B_492))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.06/2.27  tff(c_165, plain, (![A_60, B_61]: (k1_enumset1(A_60, A_60, B_61)=k2_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.06/2.27  tff(c_171, plain, (![B_61, A_60]: (r2_hidden(B_61, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_18])).
% 6.06/2.27  tff(c_6490, plain, (![A_389, B_390]: (k4_xboole_0(A_389, k4_xboole_0(A_389, B_390))=k3_xboole_0(A_389, B_390))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.06/2.27  tff(c_12, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.06/2.27  tff(c_6535, plain, (![B_391]: (k3_xboole_0(k1_xboole_0, B_391)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6490, c_12])).
% 6.06/2.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.06/2.27  tff(c_6540, plain, (![B_391]: (k3_xboole_0(B_391, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6535, c_2])).
% 6.06/2.27  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.06/2.27  tff(c_6451, plain, (![A_386, B_387]: (k5_xboole_0(A_386, k4_xboole_0(B_387, A_386))=k2_xboole_0(A_386, B_387))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.06/2.27  tff(c_6472, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k2_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_6451])).
% 6.06/2.27  tff(c_6475, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6472])).
% 6.06/2.27  tff(c_6591, plain, (![A_393, B_394]: (k5_xboole_0(A_393, k3_xboole_0(A_393, B_394))=k4_xboole_0(A_393, B_394))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.06/2.27  tff(c_6600, plain, (![B_391]: (k5_xboole_0(B_391, k1_xboole_0)=k4_xboole_0(B_391, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6540, c_6591])).
% 6.06/2.27  tff(c_6617, plain, (![B_395]: (k4_xboole_0(B_395, k1_xboole_0)=B_395)), inference(demodulation, [status(thm), theory('equality')], [c_6475, c_6600])).
% 6.06/2.27  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.06/2.27  tff(c_6623, plain, (![B_395]: (k4_xboole_0(B_395, B_395)=k3_xboole_0(B_395, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6617, c_10])).
% 6.06/2.27  tff(c_6642, plain, (![B_395]: (k4_xboole_0(B_395, B_395)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6540, c_6623])).
% 6.06/2.27  tff(c_5297, plain, (![A_310, B_311]: (k4_xboole_0(A_310, k4_xboole_0(A_310, B_311))=k3_xboole_0(A_310, B_311))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.06/2.27  tff(c_5342, plain, (![B_312]: (k3_xboole_0(k1_xboole_0, B_312)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5297, c_12])).
% 6.06/2.27  tff(c_5360, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_5342])).
% 6.06/2.27  tff(c_218, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.06/2.27  tff(c_230, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=k2_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_218])).
% 6.06/2.27  tff(c_233, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_230])).
% 6.06/2.27  tff(c_5384, plain, (![A_315]: (k3_xboole_0(A_315, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_5342])).
% 6.06/2.27  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.06/2.27  tff(c_5389, plain, (![A_315]: (k5_xboole_0(A_315, k1_xboole_0)=k4_xboole_0(A_315, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5384, c_4])).
% 6.06/2.27  tff(c_5424, plain, (![A_316]: (k4_xboole_0(A_316, k1_xboole_0)=A_316)), inference(demodulation, [status(thm), theory('equality')], [c_233, c_5389])).
% 6.06/2.27  tff(c_5430, plain, (![A_316]: (k4_xboole_0(A_316, A_316)=k3_xboole_0(A_316, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5424, c_10])).
% 6.06/2.27  tff(c_5449, plain, (![A_316]: (k4_xboole_0(A_316, A_316)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5360, c_5430])).
% 6.06/2.27  tff(c_78, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.27  tff(c_155, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_78])).
% 6.06/2.27  tff(c_74, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.27  tff(c_267, plain, (k1_tarski('#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_74])).
% 6.06/2.27  tff(c_70, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k1_tarski('#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.27  tff(c_188, plain, (k1_tarski('#skF_8')!='#skF_6'), inference(splitLeft, [status(thm)], [c_70])).
% 6.06/2.27  tff(c_66, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k2_tarski('#skF_7', '#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.27  tff(c_396, plain, (k2_tarski('#skF_7', '#skF_8')!='#skF_6'), inference(splitLeft, [status(thm)], [c_66])).
% 6.06/2.27  tff(c_283, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.06/2.27  tff(c_322, plain, (![B_80]: (k3_xboole_0(k1_xboole_0, B_80)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_283, c_12])).
% 6.06/2.27  tff(c_358, plain, (![A_84]: (k3_xboole_0(A_84, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_322])).
% 6.06/2.27  tff(c_366, plain, (![A_84]: (k5_xboole_0(A_84, k1_xboole_0)=k4_xboole_0(A_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_358, c_4])).
% 6.06/2.27  tff(c_388, plain, (![A_84]: (k4_xboole_0(A_84, k1_xboole_0)=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_233, c_366])).
% 6.06/2.27  tff(c_343, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_322])).
% 6.06/2.27  tff(c_399, plain, (![A_85]: (k4_xboole_0(A_85, k1_xboole_0)=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_233, c_366])).
% 6.06/2.27  tff(c_405, plain, (![A_85]: (k4_xboole_0(A_85, A_85)=k3_xboole_0(A_85, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_399, c_10])).
% 6.06/2.27  tff(c_424, plain, (![A_85]: (k4_xboole_0(A_85, A_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_405])).
% 6.06/2.27  tff(c_84, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.27  tff(c_1665, plain, (k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_84])).
% 6.06/2.27  tff(c_1669, plain, (k3_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k4_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1665, c_10])).
% 6.06/2.27  tff(c_1678, plain, (k3_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_1669])).
% 6.06/2.27  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.06/2.27  tff(c_617, plain, (![A_94, B_95]: (r1_tarski(k3_xboole_0(A_94, B_95), A_94))), inference(superposition, [status(thm), theory('equality')], [c_283, c_8])).
% 6.06/2.27  tff(c_629, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_617])).
% 6.06/2.27  tff(c_1691, plain, (r1_tarski('#skF_6', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1678, c_629])).
% 6.06/2.27  tff(c_1734, plain, (![B_148, C_149, A_150]: (k2_tarski(B_148, C_149)=A_150 | k1_tarski(C_149)=A_150 | k1_tarski(B_148)=A_150 | k1_xboole_0=A_150 | ~r1_tarski(A_150, k2_tarski(B_148, C_149)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.06/2.27  tff(c_1737, plain, (k2_tarski('#skF_7', '#skF_8')='#skF_6' | k1_tarski('#skF_8')='#skF_6' | k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1691, c_1734])).
% 6.06/2.27  tff(c_1774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_267, c_188, c_396, c_1737])).
% 6.06/2.27  tff(c_1775, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_84])).
% 6.06/2.27  tff(c_1804, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1775])).
% 6.06/2.27  tff(c_82, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.27  tff(c_579, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_82])).
% 6.06/2.27  tff(c_1805, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1804, c_579])).
% 6.06/2.27  tff(c_1808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_424, c_1805])).
% 6.06/2.27  tff(c_1809, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1775])).
% 6.06/2.27  tff(c_1811, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1809])).
% 6.06/2.27  tff(c_1832, plain, (![A_10]: (k4_xboole_0('#skF_3', A_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1811, c_1811, c_12])).
% 6.06/2.27  tff(c_1820, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1811, c_579])).
% 6.06/2.27  tff(c_1861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1832, c_1820])).
% 6.06/2.27  tff(c_1862, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_1809])).
% 6.06/2.27  tff(c_1864, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1862])).
% 6.06/2.27  tff(c_58, plain, (![A_31, B_32]: (k4_xboole_0(k1_tarski(A_31), B_32)=k1_tarski(A_31) | k4_xboole_0(k1_tarski(A_31), B_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.06/2.27  tff(c_40, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.06/2.27  tff(c_953, plain, (![A_109, C_110, B_111]: (~r2_hidden(A_109, C_110) | k4_xboole_0(k2_tarski(A_109, B_111), C_110)!=k2_tarski(A_109, B_111))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.06/2.27  tff(c_968, plain, (![A_20, C_110]: (~r2_hidden(A_20, C_110) | k4_xboole_0(k1_tarski(A_20), C_110)!=k2_tarski(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_40, c_953])).
% 6.06/2.27  tff(c_998, plain, (![A_119, C_120]: (~r2_hidden(A_119, C_120) | k4_xboole_0(k1_tarski(A_119), C_120)!=k1_tarski(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_968])).
% 6.06/2.27  tff(c_1019, plain, (![A_31, B_32]: (~r2_hidden(A_31, B_32) | k4_xboole_0(k1_tarski(A_31), B_32)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_998])).
% 6.06/2.27  tff(c_2165, plain, (![B_177]: (~r2_hidden('#skF_5', B_177) | k4_xboole_0('#skF_3', B_177)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1864, c_1019])).
% 6.06/2.27  tff(c_2199, plain, (![A_60]: (k4_xboole_0('#skF_3', k2_tarski(A_60, '#skF_5'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_171, c_2165])).
% 6.06/2.27  tff(c_2243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2199, c_579])).
% 6.06/2.27  tff(c_2244, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1862])).
% 6.06/2.27  tff(c_56, plain, (![A_29, B_30]: (k4_xboole_0(k1_tarski(A_29), k2_tarski(A_29, B_30))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.06/2.27  tff(c_2284, plain, (![B_30]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', B_30))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2244, c_56])).
% 6.06/2.27  tff(c_2387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2284, c_579])).
% 6.06/2.27  tff(c_2388, plain, (k4_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_82])).
% 6.06/2.27  tff(c_2471, plain, (k3_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))=k4_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2388, c_10])).
% 6.06/2.27  tff(c_2480, plain, (k3_xboole_0('#skF_6', k2_tarski('#skF_7', '#skF_8'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_2471])).
% 6.06/2.27  tff(c_2427, plain, (![A_186, B_187]: (r1_tarski(k3_xboole_0(A_186, B_187), A_186))), inference(superposition, [status(thm), theory('equality')], [c_283, c_8])).
% 6.06/2.27  tff(c_2439, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2427])).
% 6.06/2.27  tff(c_2503, plain, (r1_tarski('#skF_6', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2480, c_2439])).
% 6.06/2.27  tff(c_3775, plain, (![B_240, C_241, A_242]: (k2_tarski(B_240, C_241)=A_242 | k1_tarski(C_241)=A_242 | k1_tarski(B_240)=A_242 | k1_xboole_0=A_242 | ~r1_tarski(A_242, k2_tarski(B_240, C_241)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.06/2.27  tff(c_3785, plain, (k2_tarski('#skF_7', '#skF_8')='#skF_6' | k1_tarski('#skF_8')='#skF_6' | k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_2503, c_3775])).
% 6.06/2.27  tff(c_3822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_267, c_188, c_396, c_3785])).
% 6.06/2.27  tff(c_3823, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 6.06/2.27  tff(c_3859, plain, (![A_243]: (k4_xboole_0(A_243, k1_xboole_0)=A_243)), inference(demodulation, [status(thm), theory('equality')], [c_233, c_366])).
% 6.06/2.27  tff(c_3865, plain, (![A_243]: (k4_xboole_0(A_243, A_243)=k3_xboole_0(A_243, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3859, c_10])).
% 6.06/2.27  tff(c_3884, plain, (![A_243]: (k4_xboole_0(A_243, A_243)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_343, c_3865])).
% 6.06/2.27  tff(c_3824, plain, (k2_tarski('#skF_7', '#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_66])).
% 6.06/2.27  tff(c_68, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k2_tarski('#skF_7', '#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.27  tff(c_4359, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_68])).
% 6.06/2.27  tff(c_4360, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4359])).
% 6.06/2.27  tff(c_4378, plain, (![A_10]: (k4_xboole_0('#skF_3', A_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4360, c_4360, c_12])).
% 6.06/2.27  tff(c_3855, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0 | k4_xboole_0('#skF_6', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3824, c_82])).
% 6.06/2.27  tff(c_3856, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3855])).
% 6.06/2.27  tff(c_4371, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4360, c_3856])).
% 6.06/2.27  tff(c_4554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4378, c_4371])).
% 6.06/2.27  tff(c_4555, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_4359])).
% 6.06/2.27  tff(c_4780, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_4555])).
% 6.06/2.27  tff(c_4781, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4780, c_3856])).
% 6.06/2.27  tff(c_4784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3884, c_4781])).
% 6.06/2.27  tff(c_4785, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_4555])).
% 6.06/2.27  tff(c_4787, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_4785])).
% 6.06/2.27  tff(c_4808, plain, (![B_30]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', B_30))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4787, c_56])).
% 6.06/2.27  tff(c_4838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4808, c_3856])).
% 6.06/2.27  tff(c_4839, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_4785])).
% 6.06/2.27  tff(c_4129, plain, (![A_255, C_256, B_257]: (~r2_hidden(A_255, C_256) | k4_xboole_0(k2_tarski(A_255, B_257), C_256)!=k2_tarski(A_255, B_257))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.06/2.27  tff(c_4147, plain, (![A_20, C_256]: (~r2_hidden(A_20, C_256) | k4_xboole_0(k1_tarski(A_20), C_256)!=k2_tarski(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4129])).
% 6.06/2.27  tff(c_4564, plain, (![A_283, C_284]: (~r2_hidden(A_283, C_284) | k4_xboole_0(k1_tarski(A_283), C_284)!=k1_tarski(A_283))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4147])).
% 6.06/2.27  tff(c_4586, plain, (![A_31, B_32]: (~r2_hidden(A_31, B_32) | k4_xboole_0(k1_tarski(A_31), B_32)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_4564])).
% 6.06/2.27  tff(c_4987, plain, (![B_299]: (~r2_hidden('#skF_5', B_299) | k4_xboole_0('#skF_3', B_299)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4839, c_4586])).
% 6.06/2.27  tff(c_5021, plain, (![A_60]: (k4_xboole_0('#skF_3', k2_tarski(A_60, '#skF_5'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_171, c_4987])).
% 6.06/2.27  tff(c_5028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5021, c_3856])).
% 6.06/2.27  tff(c_5030, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_3855])).
% 6.06/2.27  tff(c_5199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3823, c_5030])).
% 6.06/2.27  tff(c_5201, plain, (k1_tarski('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_74])).
% 6.06/2.27  tff(c_76, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski('#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.27  tff(c_5543, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5201, c_76])).
% 6.06/2.27  tff(c_5544, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5543])).
% 6.06/2.27  tff(c_5556, plain, (![A_10]: (k4_xboole_0('#skF_3', A_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5544, c_5544, c_12])).
% 6.06/2.27  tff(c_5200, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 6.06/2.27  tff(c_5551, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5544, c_5200])).
% 6.06/2.27  tff(c_5599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5556, c_5551])).
% 6.06/2.27  tff(c_5600, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_5543])).
% 6.06/2.27  tff(c_5732, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_5600])).
% 6.06/2.27  tff(c_5733, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5732, c_5200])).
% 6.06/2.27  tff(c_5736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5449, c_5733])).
% 6.06/2.27  tff(c_5737, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_5600])).
% 6.06/2.27  tff(c_5739, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_5737])).
% 6.06/2.27  tff(c_5744, plain, (![B_30]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', B_30))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5739, c_56])).
% 6.06/2.27  tff(c_5771, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5744, c_5200])).
% 6.06/2.27  tff(c_5772, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_5737])).
% 6.06/2.27  tff(c_5905, plain, (![B_342, C_343, A_344]: (~r2_hidden(B_342, C_343) | k4_xboole_0(k2_tarski(A_344, B_342), C_343)!=k2_tarski(A_344, B_342))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.06/2.27  tff(c_5920, plain, (![A_20, C_343]: (~r2_hidden(A_20, C_343) | k4_xboole_0(k1_tarski(A_20), C_343)!=k2_tarski(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_40, c_5905])).
% 6.06/2.27  tff(c_5992, plain, (![A_352, C_353]: (~r2_hidden(A_352, C_353) | k4_xboole_0(k1_tarski(A_352), C_353)!=k1_tarski(A_352))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5920])).
% 6.06/2.27  tff(c_5995, plain, (![C_353]: (~r2_hidden('#skF_5', C_353) | k4_xboole_0('#skF_3', C_353)!=k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5772, c_5992])).
% 6.06/2.27  tff(c_6021, plain, (![C_354]: (~r2_hidden('#skF_5', C_354) | k4_xboole_0('#skF_3', C_354)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5772, c_5995])).
% 6.06/2.27  tff(c_6055, plain, (![A_60]: (k4_xboole_0('#skF_3', k2_tarski(A_60, '#skF_5'))!='#skF_3')), inference(resolution, [status(thm)], [c_171, c_6021])).
% 6.06/2.27  tff(c_6173, plain, (![A_373, B_374]: (k4_xboole_0(k1_tarski(A_373), B_374)=k1_tarski(A_373) | k4_xboole_0(k1_tarski(A_373), B_374)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.06/2.27  tff(c_6210, plain, (![B_374]: (k4_xboole_0('#skF_3', B_374)=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_5'), B_374)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5772, c_6173])).
% 6.06/2.27  tff(c_6256, plain, (![B_375]: (k4_xboole_0('#skF_3', B_375)='#skF_3' | k4_xboole_0('#skF_3', B_375)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5772, c_5772, c_6210])).
% 6.06/2.27  tff(c_6292, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6256, c_5200])).
% 6.06/2.27  tff(c_6335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6055, c_6292])).
% 6.06/2.27  tff(c_6337, plain, (k1_tarski('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_70])).
% 6.06/2.27  tff(c_72, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_tarski('#skF_8')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.27  tff(c_6792, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6337, c_72])).
% 6.06/2.27  tff(c_6793, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_6792])).
% 6.06/2.27  tff(c_6806, plain, (![A_10]: (k4_xboole_0('#skF_3', A_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6793, c_6793, c_12])).
% 6.06/2.27  tff(c_6336, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 6.06/2.27  tff(c_6803, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6793, c_6336])).
% 6.06/2.27  tff(c_6859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6806, c_6803])).
% 6.06/2.27  tff(c_6860, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_6792])).
% 6.06/2.27  tff(c_7013, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_6860])).
% 6.06/2.27  tff(c_7014, plain, (k4_xboole_0('#skF_3', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7013, c_6336])).
% 6.06/2.27  tff(c_7017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6642, c_7014])).
% 6.06/2.27  tff(c_7018, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_6860])).
% 6.06/2.27  tff(c_7020, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_7018])).
% 6.06/2.27  tff(c_7026, plain, (![B_30]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', B_30))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7020, c_56])).
% 6.06/2.27  tff(c_7126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7026, c_6336])).
% 6.06/2.27  tff(c_7127, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_7018])).
% 6.06/2.27  tff(c_7210, plain, (![A_424, C_425, B_426]: (~r2_hidden(A_424, C_425) | k4_xboole_0(k2_tarski(A_424, B_426), C_425)!=k2_tarski(A_424, B_426))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.06/2.27  tff(c_7225, plain, (![A_20, C_425]: (~r2_hidden(A_20, C_425) | k4_xboole_0(k1_tarski(A_20), C_425)!=k2_tarski(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_40, c_7210])).
% 6.06/2.27  tff(c_7255, plain, (![A_432, C_433]: (~r2_hidden(A_432, C_433) | k4_xboole_0(k1_tarski(A_432), C_433)!=k1_tarski(A_432))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7225])).
% 6.06/2.27  tff(c_7258, plain, (![C_433]: (~r2_hidden('#skF_5', C_433) | k4_xboole_0('#skF_3', C_433)!=k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7127, c_7255])).
% 6.06/2.27  tff(c_7284, plain, (![C_434]: (~r2_hidden('#skF_5', C_434) | k4_xboole_0('#skF_3', C_434)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7127, c_7258])).
% 6.06/2.27  tff(c_7318, plain, (![A_60]: (k4_xboole_0('#skF_3', k2_tarski(A_60, '#skF_5'))!='#skF_3')), inference(resolution, [status(thm)], [c_171, c_7284])).
% 6.06/2.27  tff(c_7452, plain, (![A_454, B_455]: (k4_xboole_0(k1_tarski(A_454), B_455)=k1_tarski(A_454) | k4_xboole_0(k1_tarski(A_454), B_455)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.06/2.27  tff(c_7489, plain, (![B_455]: (k4_xboole_0('#skF_3', B_455)=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_5'), B_455)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7127, c_7452])).
% 6.06/2.27  tff(c_7535, plain, (![B_456]: (k4_xboole_0('#skF_3', B_456)='#skF_3' | k4_xboole_0('#skF_3', B_456)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7127, c_7127, c_7489])).
% 6.06/2.27  tff(c_7574, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7535, c_6336])).
% 6.06/2.27  tff(c_7615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7318, c_7574])).
% 6.06/2.27  tff(c_7617, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_78])).
% 6.06/2.27  tff(c_7622, plain, (![A_10]: (k4_xboole_0('#skF_6', A_10)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7617, c_7617, c_12])).
% 6.06/2.27  tff(c_7813, plain, (![B_493]: (k3_xboole_0('#skF_6', B_493)='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7774, c_7622])).
% 6.06/2.27  tff(c_7821, plain, (![B_493]: (k3_xboole_0(B_493, '#skF_6')='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7813, c_2])).
% 6.06/2.27  tff(c_7621, plain, (![A_5]: (k2_xboole_0(A_5, '#skF_6')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_7617, c_6])).
% 6.06/2.27  tff(c_7731, plain, (![A_486, B_487]: (k5_xboole_0(A_486, k4_xboole_0(B_487, A_486))=k2_xboole_0(A_486, B_487))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.06/2.27  tff(c_7746, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_6')=k2_xboole_0(A_10, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7622, c_7731])).
% 6.06/2.27  tff(c_7749, plain, (![A_10]: (k5_xboole_0(A_10, '#skF_6')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_7621, c_7746])).
% 6.06/2.27  tff(c_7841, plain, (![B_494]: (k3_xboole_0(B_494, '#skF_6')='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7813, c_2])).
% 6.06/2.27  tff(c_7849, plain, (![B_494]: (k5_xboole_0(B_494, '#skF_6')=k4_xboole_0(B_494, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7841, c_4])).
% 6.06/2.27  tff(c_7881, plain, (![B_495]: (k4_xboole_0(B_495, '#skF_6')=B_495)), inference(demodulation, [status(thm), theory('equality')], [c_7749, c_7849])).
% 6.06/2.27  tff(c_7887, plain, (![B_495]: (k4_xboole_0(B_495, B_495)=k3_xboole_0(B_495, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7881, c_10])).
% 6.06/2.27  tff(c_7906, plain, (![B_495]: (k4_xboole_0(B_495, B_495)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7821, c_7887])).
% 6.06/2.27  tff(c_80, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.06/2.27  tff(c_7964, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3' | '#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7617, c_7617, c_80])).
% 6.06/2.27  tff(c_7965, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_7964])).
% 6.06/2.27  tff(c_7975, plain, (![A_10]: (k4_xboole_0('#skF_3', A_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7965, c_7965, c_7622])).
% 6.06/2.27  tff(c_7616, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 6.06/2.27  tff(c_7660, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7617, c_7616])).
% 6.06/2.27  tff(c_7973, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7965, c_7660])).
% 6.06/2.27  tff(c_8100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7975, c_7973])).
% 6.06/2.27  tff(c_8101, plain, (k1_tarski('#skF_4')='#skF_3' | k1_tarski('#skF_5')='#skF_3' | k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_7964])).
% 6.06/2.27  tff(c_8264, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_8101])).
% 6.06/2.27  tff(c_8265, plain, (k4_xboole_0('#skF_3', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8264, c_7660])).
% 6.06/2.27  tff(c_8268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7906, c_8265])).
% 6.06/2.27  tff(c_8269, plain, (k1_tarski('#skF_5')='#skF_3' | k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_8101])).
% 6.06/2.27  tff(c_8271, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_8269])).
% 6.06/2.27  tff(c_7666, plain, (![A_29, B_30]: (k4_xboole_0(k1_tarski(A_29), k2_tarski(A_29, B_30))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7617, c_56])).
% 6.06/2.27  tff(c_8280, plain, (![B_30]: (k4_xboole_0('#skF_3', k2_tarski('#skF_4', B_30))='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8271, c_7666])).
% 6.06/2.27  tff(c_8304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8280, c_7660])).
% 6.06/2.27  tff(c_8305, plain, (k1_tarski('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_8269])).
% 6.06/2.27  tff(c_8438, plain, (![A_524, C_525, B_526]: (~r2_hidden(A_524, C_525) | k4_xboole_0(k2_tarski(A_524, B_526), C_525)!=k2_tarski(A_524, B_526))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.06/2.27  tff(c_8453, plain, (![A_20, C_525]: (~r2_hidden(A_20, C_525) | k4_xboole_0(k1_tarski(A_20), C_525)!=k2_tarski(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_40, c_8438])).
% 6.06/2.27  tff(c_8481, plain, (![A_532, C_533]: (~r2_hidden(A_532, C_533) | k4_xboole_0(k1_tarski(A_532), C_533)!=k1_tarski(A_532))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8453])).
% 6.06/2.27  tff(c_8484, plain, (![C_533]: (~r2_hidden('#skF_5', C_533) | k4_xboole_0('#skF_3', C_533)!=k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8305, c_8481])).
% 6.06/2.27  tff(c_8506, plain, (![C_534]: (~r2_hidden('#skF_5', C_534) | k4_xboole_0('#skF_3', C_534)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8305, c_8484])).
% 6.06/2.27  tff(c_8540, plain, (![A_479]: (k4_xboole_0('#skF_3', k2_tarski(A_479, '#skF_5'))!='#skF_3')), inference(resolution, [status(thm)], [c_7707, c_8506])).
% 6.06/2.27  tff(c_8563, plain, (![A_538, B_539]: (k4_xboole_0(k1_tarski(A_538), B_539)=k1_tarski(A_538) | k4_xboole_0(k1_tarski(A_538), B_539)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7617, c_58])).
% 6.06/2.27  tff(c_8600, plain, (![B_539]: (k4_xboole_0('#skF_3', B_539)=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_5'), B_539)='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8305, c_8563])).
% 6.06/2.27  tff(c_8654, plain, (![B_544]: (k4_xboole_0('#skF_3', B_544)='#skF_3' | k4_xboole_0('#skF_3', B_544)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8305, c_8305, c_8600])).
% 6.06/2.27  tff(c_8693, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_4', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8654, c_7660])).
% 6.06/2.27  tff(c_8734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8540, c_8693])).
% 6.06/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.06/2.27  
% 6.06/2.27  Inference rules
% 6.06/2.27  ----------------------
% 6.06/2.27  #Ref     : 0
% 6.06/2.27  #Sup     : 1918
% 6.06/2.27  #Fact    : 9
% 6.06/2.27  #Define  : 0
% 6.06/2.27  #Split   : 27
% 6.06/2.27  #Chain   : 0
% 6.06/2.27  #Close   : 0
% 6.06/2.27  
% 6.06/2.27  Ordering : KBO
% 6.06/2.27  
% 6.06/2.28  Simplification rules
% 6.06/2.28  ----------------------
% 6.06/2.28  #Subsume      : 241
% 6.06/2.28  #Demod        : 1284
% 6.06/2.28  #Tautology    : 1202
% 6.06/2.28  #SimpNegUnit  : 156
% 6.06/2.28  #BackRed      : 97
% 6.06/2.28  
% 6.06/2.28  #Partial instantiations: 0
% 6.06/2.28  #Strategies tried      : 1
% 6.06/2.28  
% 6.06/2.28  Timing (in seconds)
% 6.06/2.28  ----------------------
% 6.06/2.28  Preprocessing        : 0.34
% 6.06/2.28  Parsing              : 0.17
% 6.06/2.28  CNF conversion       : 0.03
% 6.06/2.28  Main loop            : 1.12
% 6.06/2.28  Inferencing          : 0.37
% 6.06/2.28  Reduction            : 0.45
% 6.06/2.28  Demodulation         : 0.33
% 6.06/2.28  BG Simplification    : 0.04
% 6.06/2.28  Subsumption          : 0.17
% 6.06/2.28  Abstraction          : 0.05
% 6.06/2.28  MUC search           : 0.00
% 6.06/2.28  Cooper               : 0.00
% 6.06/2.28  Total                : 1.53
% 6.06/2.28  Index Insertion      : 0.00
% 6.06/2.28  Index Deletion       : 0.00
% 6.06/2.28  Index Matching       : 0.00
% 6.06/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
