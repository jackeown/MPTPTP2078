%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:40 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 261 expanded)
%              Number of leaves         :   46 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  198 ( 572 expanded)
%              Number of equality atoms :  150 ( 420 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_101,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_74,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_102,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_60,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_161,plain,(
    ! [A_89,B_90] : k1_enumset1(A_89,A_89,B_90) = k2_tarski(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_167,plain,(
    ! [B_90,A_89] : r2_hidden(B_90,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_26])).

tff(c_78,plain,(
    ! [A_39] :
      ( r2_hidden('#skF_7'(A_39),A_39)
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3797,plain,(
    ! [D_413,B_414,A_415] :
      ( r2_hidden(D_413,B_414)
      | ~ r2_hidden(D_413,k3_xboole_0(A_415,B_414)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3802,plain,(
    ! [A_415,B_414] :
      ( r2_hidden('#skF_7'(k3_xboole_0(A_415,B_414)),B_414)
      | k3_xboole_0(A_415,B_414) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_78,c_3797])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8350,plain,(
    ! [B_773,C_774,A_775] :
      ( ~ r2_hidden(B_773,C_774)
      | k4_xboole_0(k2_tarski(A_775,B_773),C_774) != k2_tarski(A_775,B_773) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8374,plain,(
    ! [B_776] : ~ r2_hidden(B_776,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_8350])).

tff(c_8388,plain,(
    ! [A_415] : k3_xboole_0(A_415,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3802,c_8374])).

tff(c_3803,plain,(
    ! [A_416,B_417] : k4_xboole_0(A_416,k4_xboole_0(A_416,B_417)) = k3_xboole_0(A_416,B_417) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3818,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3803])).

tff(c_8497,plain,(
    ! [A_780] : k4_xboole_0(A_780,A_780) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8388,c_3818])).

tff(c_66,plain,(
    ! [B_26,C_27,A_25] :
      ( ~ r2_hidden(B_26,C_27)
      | k4_xboole_0(k2_tarski(A_25,B_26),C_27) != k2_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8503,plain,(
    ! [B_26,A_25] :
      ( ~ r2_hidden(B_26,k2_tarski(A_25,B_26))
      | k2_tarski(A_25,B_26) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8497,c_66])).

tff(c_8525,plain,(
    ! [A_783,B_784] : k2_tarski(A_783,B_784) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_8503])).

tff(c_8527,plain,(
    ! [A_22] : k1_tarski(A_22) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_8525])).

tff(c_152,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_7'(A_79),A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_157,plain,(
    ! [A_17] :
      ( '#skF_7'(k1_tarski(A_17)) = A_17
      | k1_tarski(A_17) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_152,c_48])).

tff(c_8528,plain,(
    ! [A_17] : '#skF_7'(k1_tarski(A_17)) = A_17 ),
    inference(negUnitSimplification,[status(thm)],[c_8527,c_157])).

tff(c_50,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8549,plain,(
    ! [D_787,A_788,C_789,E_790] :
      ( ~ r2_hidden(D_787,A_788)
      | k3_mcart_1(C_789,D_787,E_790) != '#skF_7'(A_788)
      | k1_xboole_0 = A_788 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8567,plain,(
    ! [C_789,C_21,E_790] :
      ( k3_mcart_1(C_789,C_21,E_790) != '#skF_7'(k1_tarski(C_21))
      | k1_tarski(C_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_8549])).

tff(c_8581,plain,(
    ! [C_789,C_21,E_790] :
      ( k3_mcart_1(C_789,C_21,E_790) != C_21
      | k1_tarski(C_21) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8528,c_8567])).

tff(c_8582,plain,(
    ! [C_789,C_21,E_790] : k3_mcart_1(C_789,C_21,E_790) != C_21 ),
    inference(negUnitSimplification,[status(thm)],[c_8527,c_8581])).

tff(c_98,plain,(
    m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3894,plain,(
    ! [A_426,B_427,C_428] : k4_tarski(k4_tarski(A_426,B_427),C_428) = k3_mcart_1(A_426,B_427,C_428) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_94,plain,(
    ! [A_63,B_64] : k2_mcart_1(k4_tarski(A_63,B_64)) = B_64 ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_74,plain,(
    ! [B_37,C_38] : k2_mcart_1(k4_tarski(B_37,C_38)) != k4_tarski(B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_106,plain,(
    ! [B_37,C_38] : k4_tarski(B_37,C_38) != C_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_74])).

tff(c_3912,plain,(
    ! [A_426,B_427,C_428] : k3_mcart_1(A_426,B_427,C_428) != C_428 ),
    inference(superposition,[status(thm),theory(equality)],[c_3894,c_106])).

tff(c_209,plain,(
    ! [D_96,B_97,A_98] :
      ( r2_hidden(D_96,B_97)
      | ~ r2_hidden(D_96,k3_xboole_0(A_98,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_406,plain,(
    ! [A_135,B_136] :
      ( r2_hidden('#skF_7'(k3_xboole_0(A_135,B_136)),B_136)
      | k3_xboole_0(A_135,B_136) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_78,c_209])).

tff(c_339,plain,(
    ! [A_121,C_122,B_123] :
      ( ~ r2_hidden(A_121,C_122)
      | k4_xboole_0(k2_tarski(A_121,B_123),C_122) != k2_tarski(A_121,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_362,plain,(
    ! [A_121] : ~ r2_hidden(A_121,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_339])).

tff(c_426,plain,(
    ! [A_135] : k3_xboole_0(A_135,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_406,c_362])).

tff(c_28,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_170,plain,(
    ! [A_89,B_90] : r2_hidden(A_89,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_28])).

tff(c_215,plain,(
    ! [A_99,B_100] : k4_xboole_0(A_99,k4_xboole_0(A_99,B_100)) = k3_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_230,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_215])).

tff(c_347,plain,(
    ! [A_121,B_123] :
      ( ~ r2_hidden(A_121,k2_tarski(A_121,B_123))
      | k3_xboole_0(k2_tarski(A_121,B_123),k1_xboole_0) != k2_tarski(A_121,B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_339])).

tff(c_379,plain,(
    ! [A_128,B_129] : k3_xboole_0(k2_tarski(A_128,B_129),k1_xboole_0) != k2_tarski(A_128,B_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_347])).

tff(c_382,plain,(
    ! [A_22] : k3_xboole_0(k1_tarski(A_22),k1_xboole_0) != k2_tarski(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_379])).

tff(c_383,plain,(
    ! [A_22] : k3_xboole_0(k1_tarski(A_22),k1_xboole_0) != k1_tarski(A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_382])).

tff(c_432,plain,(
    ! [A_22] : k1_tarski(A_22) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_383])).

tff(c_457,plain,(
    ! [A_17] : '#skF_7'(k1_tarski(A_17)) = A_17 ),
    inference(negUnitSimplification,[status(thm)],[c_432,c_157])).

tff(c_604,plain,(
    ! [C_152,A_153,D_154,E_155] :
      ( ~ r2_hidden(C_152,A_153)
      | k3_mcart_1(C_152,D_154,E_155) != '#skF_7'(A_153)
      | k1_xboole_0 = A_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_624,plain,(
    ! [C_21,D_154,E_155] :
      ( k3_mcart_1(C_21,D_154,E_155) != '#skF_7'(k1_tarski(C_21))
      | k1_tarski(C_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_604])).

tff(c_639,plain,(
    ! [C_21,D_154,E_155] :
      ( k3_mcart_1(C_21,D_154,E_155) != C_21
      | k1_tarski(C_21) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_624])).

tff(c_640,plain,(
    ! [C_21,D_154,E_155] : k3_mcart_1(C_21,D_154,E_155) != C_21 ),
    inference(negUnitSimplification,[status(thm)],[c_432,c_639])).

tff(c_96,plain,
    ( k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11'
    | k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11'
    | k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_189,plain,(
    k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_2338,plain,(
    ! [A_335,B_336,C_337,D_338] :
      ( k7_mcart_1(A_335,B_336,C_337,D_338) = k2_mcart_1(D_338)
      | ~ m1_subset_1(D_338,k3_zfmisc_1(A_335,B_336,C_337))
      | k1_xboole_0 = C_337
      | k1_xboole_0 = B_336
      | k1_xboole_0 = A_335 ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2344,plain,
    ( k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11')
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_98,c_2338])).

tff(c_2347,plain,(
    k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_102,c_100,c_2344])).

tff(c_3697,plain,(
    ! [A_408,B_409,C_410,D_411] :
      ( k3_mcart_1(k5_mcart_1(A_408,B_409,C_410,D_411),k6_mcart_1(A_408,B_409,C_410,D_411),k7_mcart_1(A_408,B_409,C_410,D_411)) = D_411
      | ~ m1_subset_1(D_411,k3_zfmisc_1(A_408,B_409,C_410))
      | k1_xboole_0 = C_410
      | k1_xboole_0 = B_409
      | k1_xboole_0 = A_408 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3766,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k2_mcart_1('#skF_11')) = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2347,c_3697])).

tff(c_3777,plain,
    ( k3_mcart_1('#skF_11',k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k2_mcart_1('#skF_11')) = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_189,c_3766])).

tff(c_3779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_102,c_100,c_640,c_3777])).

tff(c_3780,plain,
    ( k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11'
    | k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_3858,plain,(
    k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_3780])).

tff(c_8114,plain,(
    ! [A_739,B_740,C_741,D_742] :
      ( k3_mcart_1(k5_mcart_1(A_739,B_740,C_741,D_742),k6_mcart_1(A_739,B_740,C_741,D_742),k7_mcart_1(A_739,B_740,C_741,D_742)) = D_742
      | ~ m1_subset_1(D_742,k3_zfmisc_1(A_739,B_740,C_741))
      | k1_xboole_0 = C_741
      | k1_xboole_0 = B_740
      | k1_xboole_0 = A_739 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8183,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),'#skF_11') = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_3858,c_8114])).

tff(c_8191,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),'#skF_11') = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_8183])).

tff(c_8193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_102,c_100,c_3912,c_8191])).

tff(c_8194,plain,(
    k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_3780])).

tff(c_10013,plain,(
    ! [A_950,B_951,C_952,D_953] :
      ( k7_mcart_1(A_950,B_951,C_952,D_953) = k2_mcart_1(D_953)
      | ~ m1_subset_1(D_953,k3_zfmisc_1(A_950,B_951,C_952))
      | k1_xboole_0 = C_952
      | k1_xboole_0 = B_951
      | k1_xboole_0 = A_950 ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_10019,plain,
    ( k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11')
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_98,c_10013])).

tff(c_10022,plain,(
    k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_102,c_100,c_10019])).

tff(c_11952,plain,(
    ! [A_1063,B_1064,C_1065,D_1066] :
      ( k3_mcart_1(k5_mcart_1(A_1063,B_1064,C_1065,D_1066),k6_mcart_1(A_1063,B_1064,C_1065,D_1066),k7_mcart_1(A_1063,B_1064,C_1065,D_1066)) = D_1066
      | ~ m1_subset_1(D_1066,k3_zfmisc_1(A_1063,B_1064,C_1065))
      | k1_xboole_0 = C_1065
      | k1_xboole_0 = B_1064
      | k1_xboole_0 = A_1063 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_12021,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k2_mcart_1('#skF_11')) = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_10022,c_11952])).

tff(c_12032,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),'#skF_11',k2_mcart_1('#skF_11')) = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_8194,c_12021])).

tff(c_12034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_102,c_100,c_8582,c_12032])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.75/2.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/2.83  
% 7.75/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/2.83  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 7.75/2.83  
% 7.75/2.83  %Foreground sorts:
% 7.75/2.83  
% 7.75/2.83  
% 7.75/2.83  %Background operators:
% 7.75/2.83  
% 7.75/2.83  
% 7.75/2.83  %Foreground operators:
% 7.75/2.83  tff('#skF_7', type, '#skF_7': $i > $i).
% 7.75/2.83  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.75/2.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.75/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.75/2.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.75/2.83  tff('#skF_11', type, '#skF_11': $i).
% 7.75/2.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.75/2.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.75/2.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.75/2.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.75/2.83  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.75/2.83  tff('#skF_10', type, '#skF_10': $i).
% 7.75/2.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.75/2.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.75/2.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.75/2.83  tff('#skF_9', type, '#skF_9': $i).
% 7.75/2.83  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 7.75/2.83  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.75/2.83  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.75/2.83  tff('#skF_8', type, '#skF_8': $i).
% 7.75/2.83  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 7.75/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.75/2.83  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.75/2.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.75/2.83  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 7.75/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.75/2.83  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.75/2.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.75/2.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.75/2.83  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.75/2.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.75/2.83  
% 7.75/2.85  tff(f_165, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 7.75/2.85  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.75/2.85  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.75/2.85  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.75/2.85  tff(f_101, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 7.75/2.85  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.75/2.85  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.75/2.85  tff(f_72, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 7.75/2.85  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.75/2.85  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 7.75/2.85  tff(f_74, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 7.75/2.85  tff(f_141, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 7.75/2.85  tff(f_85, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 7.75/2.85  tff(f_137, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 7.75/2.85  tff(f_117, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 7.75/2.85  tff(c_104, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.75/2.85  tff(c_102, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.75/2.85  tff(c_100, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.75/2.85  tff(c_60, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.75/2.85  tff(c_161, plain, (![A_89, B_90]: (k1_enumset1(A_89, A_89, B_90)=k2_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.75/2.85  tff(c_26, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.75/2.85  tff(c_167, plain, (![B_90, A_89]: (r2_hidden(B_90, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_26])).
% 7.75/2.85  tff(c_78, plain, (![A_39]: (r2_hidden('#skF_7'(A_39), A_39) | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.75/2.85  tff(c_3797, plain, (![D_413, B_414, A_415]: (r2_hidden(D_413, B_414) | ~r2_hidden(D_413, k3_xboole_0(A_415, B_414)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.75/2.85  tff(c_3802, plain, (![A_415, B_414]: (r2_hidden('#skF_7'(k3_xboole_0(A_415, B_414)), B_414) | k3_xboole_0(A_415, B_414)=k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_3797])).
% 7.75/2.85  tff(c_20, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.75/2.85  tff(c_8350, plain, (![B_773, C_774, A_775]: (~r2_hidden(B_773, C_774) | k4_xboole_0(k2_tarski(A_775, B_773), C_774)!=k2_tarski(A_775, B_773))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.75/2.85  tff(c_8374, plain, (![B_776]: (~r2_hidden(B_776, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_8350])).
% 7.75/2.85  tff(c_8388, plain, (![A_415]: (k3_xboole_0(A_415, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3802, c_8374])).
% 7.75/2.85  tff(c_3803, plain, (![A_416, B_417]: (k4_xboole_0(A_416, k4_xboole_0(A_416, B_417))=k3_xboole_0(A_416, B_417))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.75/2.85  tff(c_3818, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3803])).
% 7.75/2.85  tff(c_8497, plain, (![A_780]: (k4_xboole_0(A_780, A_780)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8388, c_3818])).
% 7.75/2.85  tff(c_66, plain, (![B_26, C_27, A_25]: (~r2_hidden(B_26, C_27) | k4_xboole_0(k2_tarski(A_25, B_26), C_27)!=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.75/2.85  tff(c_8503, plain, (![B_26, A_25]: (~r2_hidden(B_26, k2_tarski(A_25, B_26)) | k2_tarski(A_25, B_26)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8497, c_66])).
% 7.75/2.85  tff(c_8525, plain, (![A_783, B_784]: (k2_tarski(A_783, B_784)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_167, c_8503])).
% 7.75/2.85  tff(c_8527, plain, (![A_22]: (k1_tarski(A_22)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_8525])).
% 7.75/2.85  tff(c_152, plain, (![A_79]: (r2_hidden('#skF_7'(A_79), A_79) | k1_xboole_0=A_79)), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.75/2.85  tff(c_48, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.75/2.85  tff(c_157, plain, (![A_17]: ('#skF_7'(k1_tarski(A_17))=A_17 | k1_tarski(A_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_152, c_48])).
% 7.75/2.85  tff(c_8528, plain, (![A_17]: ('#skF_7'(k1_tarski(A_17))=A_17)), inference(negUnitSimplification, [status(thm)], [c_8527, c_157])).
% 7.75/2.85  tff(c_50, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.75/2.85  tff(c_8549, plain, (![D_787, A_788, C_789, E_790]: (~r2_hidden(D_787, A_788) | k3_mcart_1(C_789, D_787, E_790)!='#skF_7'(A_788) | k1_xboole_0=A_788)), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.75/2.85  tff(c_8567, plain, (![C_789, C_21, E_790]: (k3_mcart_1(C_789, C_21, E_790)!='#skF_7'(k1_tarski(C_21)) | k1_tarski(C_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_8549])).
% 7.75/2.85  tff(c_8581, plain, (![C_789, C_21, E_790]: (k3_mcart_1(C_789, C_21, E_790)!=C_21 | k1_tarski(C_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8528, c_8567])).
% 7.75/2.85  tff(c_8582, plain, (![C_789, C_21, E_790]: (k3_mcart_1(C_789, C_21, E_790)!=C_21)), inference(negUnitSimplification, [status(thm)], [c_8527, c_8581])).
% 7.75/2.85  tff(c_98, plain, (m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.75/2.85  tff(c_3894, plain, (![A_426, B_427, C_428]: (k4_tarski(k4_tarski(A_426, B_427), C_428)=k3_mcart_1(A_426, B_427, C_428))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.75/2.85  tff(c_94, plain, (![A_63, B_64]: (k2_mcart_1(k4_tarski(A_63, B_64))=B_64)), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.75/2.85  tff(c_74, plain, (![B_37, C_38]: (k2_mcart_1(k4_tarski(B_37, C_38))!=k4_tarski(B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.75/2.85  tff(c_106, plain, (![B_37, C_38]: (k4_tarski(B_37, C_38)!=C_38)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_74])).
% 7.75/2.85  tff(c_3912, plain, (![A_426, B_427, C_428]: (k3_mcart_1(A_426, B_427, C_428)!=C_428)), inference(superposition, [status(thm), theory('equality')], [c_3894, c_106])).
% 7.75/2.85  tff(c_209, plain, (![D_96, B_97, A_98]: (r2_hidden(D_96, B_97) | ~r2_hidden(D_96, k3_xboole_0(A_98, B_97)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.75/2.85  tff(c_406, plain, (![A_135, B_136]: (r2_hidden('#skF_7'(k3_xboole_0(A_135, B_136)), B_136) | k3_xboole_0(A_135, B_136)=k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_209])).
% 7.75/2.85  tff(c_339, plain, (![A_121, C_122, B_123]: (~r2_hidden(A_121, C_122) | k4_xboole_0(k2_tarski(A_121, B_123), C_122)!=k2_tarski(A_121, B_123))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.75/2.85  tff(c_362, plain, (![A_121]: (~r2_hidden(A_121, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_339])).
% 7.75/2.85  tff(c_426, plain, (![A_135]: (k3_xboole_0(A_135, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_406, c_362])).
% 7.75/2.85  tff(c_28, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.75/2.85  tff(c_170, plain, (![A_89, B_90]: (r2_hidden(A_89, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_28])).
% 7.75/2.85  tff(c_215, plain, (![A_99, B_100]: (k4_xboole_0(A_99, k4_xboole_0(A_99, B_100))=k3_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.75/2.85  tff(c_230, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_215])).
% 7.75/2.85  tff(c_347, plain, (![A_121, B_123]: (~r2_hidden(A_121, k2_tarski(A_121, B_123)) | k3_xboole_0(k2_tarski(A_121, B_123), k1_xboole_0)!=k2_tarski(A_121, B_123))), inference(superposition, [status(thm), theory('equality')], [c_230, c_339])).
% 7.75/2.85  tff(c_379, plain, (![A_128, B_129]: (k3_xboole_0(k2_tarski(A_128, B_129), k1_xboole_0)!=k2_tarski(A_128, B_129))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_347])).
% 7.75/2.85  tff(c_382, plain, (![A_22]: (k3_xboole_0(k1_tarski(A_22), k1_xboole_0)!=k2_tarski(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_60, c_379])).
% 7.75/2.85  tff(c_383, plain, (![A_22]: (k3_xboole_0(k1_tarski(A_22), k1_xboole_0)!=k1_tarski(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_382])).
% 7.75/2.85  tff(c_432, plain, (![A_22]: (k1_tarski(A_22)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_426, c_383])).
% 7.75/2.85  tff(c_457, plain, (![A_17]: ('#skF_7'(k1_tarski(A_17))=A_17)), inference(negUnitSimplification, [status(thm)], [c_432, c_157])).
% 7.75/2.85  tff(c_604, plain, (![C_152, A_153, D_154, E_155]: (~r2_hidden(C_152, A_153) | k3_mcart_1(C_152, D_154, E_155)!='#skF_7'(A_153) | k1_xboole_0=A_153)), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.75/2.85  tff(c_624, plain, (![C_21, D_154, E_155]: (k3_mcart_1(C_21, D_154, E_155)!='#skF_7'(k1_tarski(C_21)) | k1_tarski(C_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_604])).
% 7.75/2.85  tff(c_639, plain, (![C_21, D_154, E_155]: (k3_mcart_1(C_21, D_154, E_155)!=C_21 | k1_tarski(C_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_457, c_624])).
% 7.75/2.85  tff(c_640, plain, (![C_21, D_154, E_155]: (k3_mcart_1(C_21, D_154, E_155)!=C_21)), inference(negUnitSimplification, [status(thm)], [c_432, c_639])).
% 7.75/2.85  tff(c_96, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11' | k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11' | k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(cnfTransformation, [status(thm)], [f_165])).
% 7.75/2.85  tff(c_189, plain, (k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitLeft, [status(thm)], [c_96])).
% 7.75/2.85  tff(c_2338, plain, (![A_335, B_336, C_337, D_338]: (k7_mcart_1(A_335, B_336, C_337, D_338)=k2_mcart_1(D_338) | ~m1_subset_1(D_338, k3_zfmisc_1(A_335, B_336, C_337)) | k1_xboole_0=C_337 | k1_xboole_0=B_336 | k1_xboole_0=A_335)), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.75/2.85  tff(c_2344, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11') | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_98, c_2338])).
% 7.75/2.85  tff(c_2347, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_104, c_102, c_100, c_2344])).
% 7.75/2.85  tff(c_3697, plain, (![A_408, B_409, C_410, D_411]: (k3_mcart_1(k5_mcart_1(A_408, B_409, C_410, D_411), k6_mcart_1(A_408, B_409, C_410, D_411), k7_mcart_1(A_408, B_409, C_410, D_411))=D_411 | ~m1_subset_1(D_411, k3_zfmisc_1(A_408, B_409, C_410)) | k1_xboole_0=C_410 | k1_xboole_0=B_409 | k1_xboole_0=A_408)), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.75/2.85  tff(c_3766, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k2_mcart_1('#skF_11'))='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_2347, c_3697])).
% 7.75/2.85  tff(c_3777, plain, (k3_mcart_1('#skF_11', k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k2_mcart_1('#skF_11'))='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_189, c_3766])).
% 7.75/2.85  tff(c_3779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_102, c_100, c_640, c_3777])).
% 7.75/2.85  tff(c_3780, plain, (k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11' | k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitRight, [status(thm)], [c_96])).
% 7.75/2.85  tff(c_3858, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitLeft, [status(thm)], [c_3780])).
% 7.75/2.85  tff(c_8114, plain, (![A_739, B_740, C_741, D_742]: (k3_mcart_1(k5_mcart_1(A_739, B_740, C_741, D_742), k6_mcart_1(A_739, B_740, C_741, D_742), k7_mcart_1(A_739, B_740, C_741, D_742))=D_742 | ~m1_subset_1(D_742, k3_zfmisc_1(A_739, B_740, C_741)) | k1_xboole_0=C_741 | k1_xboole_0=B_740 | k1_xboole_0=A_739)), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.75/2.85  tff(c_8183, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), '#skF_11')='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_3858, c_8114])).
% 7.75/2.85  tff(c_8191, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), '#skF_11')='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_8183])).
% 7.75/2.85  tff(c_8193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_102, c_100, c_3912, c_8191])).
% 7.75/2.85  tff(c_8194, plain, (k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitRight, [status(thm)], [c_3780])).
% 7.75/2.85  tff(c_10013, plain, (![A_950, B_951, C_952, D_953]: (k7_mcart_1(A_950, B_951, C_952, D_953)=k2_mcart_1(D_953) | ~m1_subset_1(D_953, k3_zfmisc_1(A_950, B_951, C_952)) | k1_xboole_0=C_952 | k1_xboole_0=B_951 | k1_xboole_0=A_950)), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.75/2.85  tff(c_10019, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11') | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_98, c_10013])).
% 7.75/2.85  tff(c_10022, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_104, c_102, c_100, c_10019])).
% 7.75/2.85  tff(c_11952, plain, (![A_1063, B_1064, C_1065, D_1066]: (k3_mcart_1(k5_mcart_1(A_1063, B_1064, C_1065, D_1066), k6_mcart_1(A_1063, B_1064, C_1065, D_1066), k7_mcart_1(A_1063, B_1064, C_1065, D_1066))=D_1066 | ~m1_subset_1(D_1066, k3_zfmisc_1(A_1063, B_1064, C_1065)) | k1_xboole_0=C_1065 | k1_xboole_0=B_1064 | k1_xboole_0=A_1063)), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.75/2.85  tff(c_12021, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k2_mcart_1('#skF_11'))='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_10022, c_11952])).
% 7.75/2.85  tff(c_12032, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), '#skF_11', k2_mcart_1('#skF_11'))='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_8194, c_12021])).
% 7.75/2.85  tff(c_12034, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_102, c_100, c_8582, c_12032])).
% 7.75/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/2.85  
% 7.75/2.85  Inference rules
% 7.75/2.85  ----------------------
% 7.75/2.85  #Ref     : 18
% 7.75/2.85  #Sup     : 2608
% 7.75/2.85  #Fact    : 14
% 7.75/2.85  #Define  : 0
% 7.75/2.85  #Split   : 2
% 7.75/2.85  #Chain   : 0
% 7.75/2.85  #Close   : 0
% 7.75/2.85  
% 7.75/2.85  Ordering : KBO
% 7.75/2.85  
% 7.75/2.85  Simplification rules
% 7.75/2.85  ----------------------
% 7.75/2.85  #Subsume      : 537
% 7.75/2.85  #Demod        : 1096
% 7.75/2.85  #Tautology    : 900
% 7.75/2.85  #SimpNegUnit  : 469
% 7.75/2.85  #BackRed      : 14
% 7.75/2.85  
% 7.75/2.85  #Partial instantiations: 0
% 7.75/2.85  #Strategies tried      : 1
% 7.75/2.85  
% 7.75/2.85  Timing (in seconds)
% 7.75/2.85  ----------------------
% 7.75/2.86  Preprocessing        : 0.45
% 7.75/2.86  Parsing              : 0.24
% 7.75/2.86  CNF conversion       : 0.03
% 7.75/2.86  Main loop            : 1.57
% 7.75/2.86  Inferencing          : 0.51
% 7.75/2.86  Reduction            : 0.54
% 7.75/2.86  Demodulation         : 0.35
% 7.75/2.86  BG Simplification    : 0.07
% 7.75/2.86  Subsumption          : 0.32
% 7.75/2.86  Abstraction          : 0.12
% 7.75/2.86  MUC search           : 0.00
% 7.75/2.86  Cooper               : 0.00
% 7.75/2.86  Total                : 2.06
% 7.75/2.86  Index Insertion      : 0.00
% 7.75/2.86  Index Deletion       : 0.00
% 7.75/2.86  Index Matching       : 0.00
% 7.75/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
