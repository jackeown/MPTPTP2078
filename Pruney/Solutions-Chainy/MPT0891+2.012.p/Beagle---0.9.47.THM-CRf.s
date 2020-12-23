%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:41 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.15s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 233 expanded)
%              Number of leaves         :   42 (  98 expanded)
%              Depth                    :    9
%              Number of atoms          :  167 ( 432 expanded)
%              Number of equality atoms :  124 ( 328 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_93,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_34,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_156,plain,(
    ! [A_79,B_80] : k1_enumset1(A_79,A_79,B_80) = k2_tarski(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [E_12,B_7,C_8] : r2_hidden(E_12,k1_enumset1(E_12,B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1482,plain,(
    ! [A_261,B_262] : r2_hidden(A_261,k2_tarski(A_261,B_262)) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_16])).

tff(c_1485,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1482])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1493,plain,(
    ! [A_266,B_267] : k4_xboole_0(A_266,k4_xboole_0(A_266,B_267)) = k3_xboole_0(A_266,B_267) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1512,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1493])).

tff(c_1522,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1512])).

tff(c_3192,plain,(
    ! [B_468,A_469] :
      ( ~ r2_hidden(B_468,A_469)
      | k4_xboole_0(A_469,k1_tarski(B_468)) != A_469 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3196,plain,(
    ! [B_468] :
      ( ~ r2_hidden(B_468,k1_tarski(B_468))
      | k1_tarski(B_468) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1522,c_3192])).

tff(c_3202,plain,(
    ! [B_468] : k1_tarski(B_468) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1485,c_3196])).

tff(c_56,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_3'(A_32),A_32)
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_141,plain,(
    ! [C_66,B_67] : ~ r2_hidden(C_66,k4_xboole_0(B_67,k1_tarski(C_66))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144,plain,(
    ! [C_66] : ~ r2_hidden(C_66,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_141])).

tff(c_3424,plain,(
    ! [A_508,B_509,C_510] :
      ( r2_hidden(A_508,k4_xboole_0(B_509,k1_tarski(C_510)))
      | C_510 = A_508
      | ~ r2_hidden(A_508,B_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3440,plain,(
    ! [A_508,C_510] :
      ( r2_hidden(A_508,k1_xboole_0)
      | C_510 = A_508
      | ~ r2_hidden(A_508,k1_tarski(C_510)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1522,c_3424])).

tff(c_3451,plain,(
    ! [C_511,A_512] :
      ( C_511 = A_512
      | ~ r2_hidden(A_512,k1_tarski(C_511)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_3440])).

tff(c_3458,plain,(
    ! [C_511] :
      ( '#skF_3'(k1_tarski(C_511)) = C_511
      | k1_tarski(C_511) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_3451])).

tff(c_3463,plain,(
    ! [C_511] : '#skF_3'(k1_tarski(C_511)) = C_511 ),
    inference(negUnitSimplification,[status(thm)],[c_3202,c_3458])).

tff(c_3360,plain,(
    ! [D_496,A_497,C_498,E_499] :
      ( ~ r2_hidden(D_496,A_497)
      | k3_mcart_1(C_498,D_496,E_499) != '#skF_3'(A_497)
      | k1_xboole_0 = A_497 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3364,plain,(
    ! [C_498,A_13,E_499] :
      ( k3_mcart_1(C_498,A_13,E_499) != '#skF_3'(k1_tarski(A_13))
      | k1_tarski(A_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1485,c_3360])).

tff(c_3378,plain,(
    ! [C_498,A_13,E_499] : k3_mcart_1(C_498,A_13,E_499) != '#skF_3'(k1_tarski(A_13)) ),
    inference(negUnitSimplification,[status(thm)],[c_3202,c_3364])).

tff(c_3464,plain,(
    ! [C_498,A_13,E_499] : k3_mcart_1(C_498,A_13,E_499) != A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3463,c_3378])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1710,plain,(
    ! [A_281,B_282,C_283] : k4_tarski(k4_tarski(A_281,B_282),C_283) = k3_mcart_1(A_281,B_282,C_283) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66,plain,(
    ! [A_51,B_52] : k2_mcart_1(k4_tarski(A_51,B_52)) = B_52 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_52,plain,(
    ! [B_30,C_31] : k2_mcart_1(k4_tarski(B_30,C_31)) != k4_tarski(B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_78,plain,(
    ! [B_30,C_31] : k4_tarski(B_30,C_31) != C_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_52])).

tff(c_1728,plain,(
    ! [A_281,B_282,C_283] : k3_mcart_1(A_281,B_282,C_283) != C_283 ),
    inference(superposition,[status(thm),theory(equality)],[c_1710,c_78])).

tff(c_175,plain,(
    ! [A_81,B_82] : r2_hidden(A_81,k2_tarski(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_16])).

tff(c_178,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_175])).

tff(c_190,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k4_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_209,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_190])).

tff(c_219,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_209])).

tff(c_269,plain,(
    ! [B_90,A_91] :
      ( ~ r2_hidden(B_90,A_91)
      | k4_xboole_0(A_91,k1_tarski(B_90)) != A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_273,plain,(
    ! [B_90] :
      ( ~ r2_hidden(B_90,k1_tarski(B_90))
      | k1_tarski(B_90) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_269])).

tff(c_279,plain,(
    ! [B_90] : k1_tarski(B_90) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_273])).

tff(c_642,plain,(
    ! [A_145,B_146,C_147] :
      ( r2_hidden(A_145,k4_xboole_0(B_146,k1_tarski(C_147)))
      | C_147 = A_145
      | ~ r2_hidden(A_145,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_660,plain,(
    ! [A_145,C_147] :
      ( r2_hidden(A_145,k1_xboole_0)
      | C_147 = A_145
      | ~ r2_hidden(A_145,k1_tarski(C_147)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_642])).

tff(c_672,plain,(
    ! [C_148,A_149] :
      ( C_148 = A_149
      | ~ r2_hidden(A_149,k1_tarski(C_148)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_660])).

tff(c_679,plain,(
    ! [C_148] :
      ( '#skF_3'(k1_tarski(C_148)) = C_148
      | k1_tarski(C_148) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_672])).

tff(c_684,plain,(
    ! [C_148] : '#skF_3'(k1_tarski(C_148)) = C_148 ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_679])).

tff(c_549,plain,(
    ! [C_123,A_124,D_125,E_126] :
      ( ~ r2_hidden(C_123,A_124)
      | k3_mcart_1(C_123,D_125,E_126) != '#skF_3'(A_124)
      | k1_xboole_0 = A_124 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_553,plain,(
    ! [A_13,D_125,E_126] :
      ( k3_mcart_1(A_13,D_125,E_126) != '#skF_3'(k1_tarski(A_13))
      | k1_tarski(A_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_178,c_549])).

tff(c_567,plain,(
    ! [A_13,D_125,E_126] : k3_mcart_1(A_13,D_125,E_126) != '#skF_3'(k1_tarski(A_13)) ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_553])).

tff(c_686,plain,(
    ! [A_13,D_125,E_126] : k3_mcart_1(A_13,D_125,E_126) != A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_567])).

tff(c_68,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_174,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_1416,plain,(
    ! [A_257,B_258,C_259,D_260] :
      ( k3_mcart_1(k5_mcart_1(A_257,B_258,C_259,D_260),k6_mcart_1(A_257,B_258,C_259,D_260),k7_mcart_1(A_257,B_258,C_259,D_260)) = D_260
      | ~ m1_subset_1(D_260,k3_zfmisc_1(A_257,B_258,C_259))
      | k1_xboole_0 = C_259
      | k1_xboole_0 = B_258
      | k1_xboole_0 = A_257 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1473,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_1416])).

tff(c_1477,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1473])).

tff(c_1479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_686,c_1477])).

tff(c_1480,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1572,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1480])).

tff(c_3080,plain,(
    ! [A_463,B_464,C_465,D_466] :
      ( k3_mcart_1(k5_mcart_1(A_463,B_464,C_465,D_466),k6_mcart_1(A_463,B_464,C_465,D_466),k7_mcart_1(A_463,B_464,C_465,D_466)) = D_466
      | ~ m1_subset_1(D_466,k3_zfmisc_1(A_463,B_464,C_465))
      | k1_xboole_0 = C_465
      | k1_xboole_0 = B_464
      | k1_xboole_0 = A_463 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3149,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1572,c_3080])).

tff(c_3153,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3149])).

tff(c_3155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_1728,c_3153])).

tff(c_3156,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1480])).

tff(c_4490,plain,(
    ! [A_647,B_648,C_649,D_650] :
      ( k3_mcart_1(k5_mcart_1(A_647,B_648,C_649,D_650),k6_mcart_1(A_647,B_648,C_649,D_650),k7_mcart_1(A_647,B_648,C_649,D_650)) = D_650
      | ~ m1_subset_1(D_650,k3_zfmisc_1(A_647,B_648,C_649))
      | k1_xboole_0 = C_649
      | k1_xboole_0 = B_648
      | k1_xboole_0 = A_647 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4556,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3156,c_4490])).

tff(c_4560,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4556])).

tff(c_4562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_3464,c_4560])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/2.04  
% 5.15/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/2.04  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 5.15/2.04  
% 5.15/2.04  %Foreground sorts:
% 5.15/2.04  
% 5.15/2.04  
% 5.15/2.04  %Background operators:
% 5.15/2.04  
% 5.15/2.04  
% 5.15/2.04  %Foreground operators:
% 5.15/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.15/2.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.15/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.15/2.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.15/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.15/2.04  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.15/2.04  tff('#skF_7', type, '#skF_7': $i).
% 5.15/2.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.15/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.15/2.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.15/2.04  tff('#skF_6', type, '#skF_6': $i).
% 5.15/2.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.15/2.04  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 5.15/2.04  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.15/2.04  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 5.15/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/2.04  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.15/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.15/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.15/2.04  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.15/2.04  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 5.15/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/2.04  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.15/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.15/2.04  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.15/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.15/2.04  
% 5.15/2.06  tff(f_137, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 5.15/2.06  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.15/2.06  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.15/2.06  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.15/2.06  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 5.15/2.06  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.15/2.06  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.15/2.06  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.15/2.06  tff(f_93, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 5.15/2.06  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 5.15/2.06  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 5.15/2.06  tff(f_66, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 5.15/2.06  tff(f_113, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 5.15/2.06  tff(f_77, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 5.15/2.06  tff(f_109, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 5.15/2.06  tff(c_76, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.15/2.06  tff(c_74, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.15/2.06  tff(c_72, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.15/2.06  tff(c_34, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.15/2.06  tff(c_156, plain, (![A_79, B_80]: (k1_enumset1(A_79, A_79, B_80)=k2_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.15/2.06  tff(c_16, plain, (![E_12, B_7, C_8]: (r2_hidden(E_12, k1_enumset1(E_12, B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.15/2.06  tff(c_1482, plain, (![A_261, B_262]: (r2_hidden(A_261, k2_tarski(A_261, B_262)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_16])).
% 5.15/2.06  tff(c_1485, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1482])).
% 5.15/2.06  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.15/2.06  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.15/2.06  tff(c_1493, plain, (![A_266, B_267]: (k4_xboole_0(A_266, k4_xboole_0(A_266, B_267))=k3_xboole_0(A_266, B_267))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.15/2.06  tff(c_1512, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1493])).
% 5.15/2.06  tff(c_1522, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1512])).
% 5.15/2.06  tff(c_3192, plain, (![B_468, A_469]: (~r2_hidden(B_468, A_469) | k4_xboole_0(A_469, k1_tarski(B_468))!=A_469)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.15/2.06  tff(c_3196, plain, (![B_468]: (~r2_hidden(B_468, k1_tarski(B_468)) | k1_tarski(B_468)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1522, c_3192])).
% 5.15/2.06  tff(c_3202, plain, (![B_468]: (k1_tarski(B_468)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1485, c_3196])).
% 5.15/2.06  tff(c_56, plain, (![A_32]: (r2_hidden('#skF_3'(A_32), A_32) | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.15/2.06  tff(c_8, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.15/2.06  tff(c_141, plain, (![C_66, B_67]: (~r2_hidden(C_66, k4_xboole_0(B_67, k1_tarski(C_66))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.15/2.06  tff(c_144, plain, (![C_66]: (~r2_hidden(C_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_141])).
% 5.15/2.06  tff(c_3424, plain, (![A_508, B_509, C_510]: (r2_hidden(A_508, k4_xboole_0(B_509, k1_tarski(C_510))) | C_510=A_508 | ~r2_hidden(A_508, B_509))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.15/2.06  tff(c_3440, plain, (![A_508, C_510]: (r2_hidden(A_508, k1_xboole_0) | C_510=A_508 | ~r2_hidden(A_508, k1_tarski(C_510)))), inference(superposition, [status(thm), theory('equality')], [c_1522, c_3424])).
% 5.15/2.06  tff(c_3451, plain, (![C_511, A_512]: (C_511=A_512 | ~r2_hidden(A_512, k1_tarski(C_511)))), inference(negUnitSimplification, [status(thm)], [c_144, c_3440])).
% 5.15/2.06  tff(c_3458, plain, (![C_511]: ('#skF_3'(k1_tarski(C_511))=C_511 | k1_tarski(C_511)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_3451])).
% 5.15/2.06  tff(c_3463, plain, (![C_511]: ('#skF_3'(k1_tarski(C_511))=C_511)), inference(negUnitSimplification, [status(thm)], [c_3202, c_3458])).
% 5.15/2.06  tff(c_3360, plain, (![D_496, A_497, C_498, E_499]: (~r2_hidden(D_496, A_497) | k3_mcart_1(C_498, D_496, E_499)!='#skF_3'(A_497) | k1_xboole_0=A_497)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.15/2.06  tff(c_3364, plain, (![C_498, A_13, E_499]: (k3_mcart_1(C_498, A_13, E_499)!='#skF_3'(k1_tarski(A_13)) | k1_tarski(A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1485, c_3360])).
% 5.15/2.06  tff(c_3378, plain, (![C_498, A_13, E_499]: (k3_mcart_1(C_498, A_13, E_499)!='#skF_3'(k1_tarski(A_13)))), inference(negUnitSimplification, [status(thm)], [c_3202, c_3364])).
% 5.15/2.06  tff(c_3464, plain, (![C_498, A_13, E_499]: (k3_mcart_1(C_498, A_13, E_499)!=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_3463, c_3378])).
% 5.15/2.06  tff(c_70, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.15/2.06  tff(c_1710, plain, (![A_281, B_282, C_283]: (k4_tarski(k4_tarski(A_281, B_282), C_283)=k3_mcart_1(A_281, B_282, C_283))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.15/2.06  tff(c_66, plain, (![A_51, B_52]: (k2_mcart_1(k4_tarski(A_51, B_52))=B_52)), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.15/2.06  tff(c_52, plain, (![B_30, C_31]: (k2_mcart_1(k4_tarski(B_30, C_31))!=k4_tarski(B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.15/2.06  tff(c_78, plain, (![B_30, C_31]: (k4_tarski(B_30, C_31)!=C_31)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_52])).
% 5.15/2.06  tff(c_1728, plain, (![A_281, B_282, C_283]: (k3_mcart_1(A_281, B_282, C_283)!=C_283)), inference(superposition, [status(thm), theory('equality')], [c_1710, c_78])).
% 5.15/2.06  tff(c_175, plain, (![A_81, B_82]: (r2_hidden(A_81, k2_tarski(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_16])).
% 5.15/2.06  tff(c_178, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_175])).
% 5.15/2.06  tff(c_190, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k4_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.15/2.06  tff(c_209, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_190])).
% 5.15/2.06  tff(c_219, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_209])).
% 5.15/2.06  tff(c_269, plain, (![B_90, A_91]: (~r2_hidden(B_90, A_91) | k4_xboole_0(A_91, k1_tarski(B_90))!=A_91)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.15/2.06  tff(c_273, plain, (![B_90]: (~r2_hidden(B_90, k1_tarski(B_90)) | k1_tarski(B_90)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_219, c_269])).
% 5.15/2.06  tff(c_279, plain, (![B_90]: (k1_tarski(B_90)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_178, c_273])).
% 5.15/2.06  tff(c_642, plain, (![A_145, B_146, C_147]: (r2_hidden(A_145, k4_xboole_0(B_146, k1_tarski(C_147))) | C_147=A_145 | ~r2_hidden(A_145, B_146))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.15/2.06  tff(c_660, plain, (![A_145, C_147]: (r2_hidden(A_145, k1_xboole_0) | C_147=A_145 | ~r2_hidden(A_145, k1_tarski(C_147)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_642])).
% 5.15/2.06  tff(c_672, plain, (![C_148, A_149]: (C_148=A_149 | ~r2_hidden(A_149, k1_tarski(C_148)))), inference(negUnitSimplification, [status(thm)], [c_144, c_660])).
% 5.15/2.06  tff(c_679, plain, (![C_148]: ('#skF_3'(k1_tarski(C_148))=C_148 | k1_tarski(C_148)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_672])).
% 5.15/2.06  tff(c_684, plain, (![C_148]: ('#skF_3'(k1_tarski(C_148))=C_148)), inference(negUnitSimplification, [status(thm)], [c_279, c_679])).
% 5.15/2.06  tff(c_549, plain, (![C_123, A_124, D_125, E_126]: (~r2_hidden(C_123, A_124) | k3_mcart_1(C_123, D_125, E_126)!='#skF_3'(A_124) | k1_xboole_0=A_124)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.15/2.06  tff(c_553, plain, (![A_13, D_125, E_126]: (k3_mcart_1(A_13, D_125, E_126)!='#skF_3'(k1_tarski(A_13)) | k1_tarski(A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_178, c_549])).
% 5.15/2.06  tff(c_567, plain, (![A_13, D_125, E_126]: (k3_mcart_1(A_13, D_125, E_126)!='#skF_3'(k1_tarski(A_13)))), inference(negUnitSimplification, [status(thm)], [c_279, c_553])).
% 5.15/2.06  tff(c_686, plain, (![A_13, D_125, E_126]: (k3_mcart_1(A_13, D_125, E_126)!=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_684, c_567])).
% 5.15/2.06  tff(c_68, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.15/2.06  tff(c_174, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_68])).
% 5.15/2.06  tff(c_1416, plain, (![A_257, B_258, C_259, D_260]: (k3_mcart_1(k5_mcart_1(A_257, B_258, C_259, D_260), k6_mcart_1(A_257, B_258, C_259, D_260), k7_mcart_1(A_257, B_258, C_259, D_260))=D_260 | ~m1_subset_1(D_260, k3_zfmisc_1(A_257, B_258, C_259)) | k1_xboole_0=C_259 | k1_xboole_0=B_258 | k1_xboole_0=A_257)), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.15/2.06  tff(c_1473, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_174, c_1416])).
% 5.15/2.06  tff(c_1477, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1473])).
% 5.15/2.06  tff(c_1479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_74, c_72, c_686, c_1477])).
% 5.15/2.06  tff(c_1480, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_68])).
% 5.15/2.06  tff(c_1572, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_1480])).
% 5.15/2.06  tff(c_3080, plain, (![A_463, B_464, C_465, D_466]: (k3_mcart_1(k5_mcart_1(A_463, B_464, C_465, D_466), k6_mcart_1(A_463, B_464, C_465, D_466), k7_mcart_1(A_463, B_464, C_465, D_466))=D_466 | ~m1_subset_1(D_466, k3_zfmisc_1(A_463, B_464, C_465)) | k1_xboole_0=C_465 | k1_xboole_0=B_464 | k1_xboole_0=A_463)), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.15/2.06  tff(c_3149, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1572, c_3080])).
% 5.15/2.06  tff(c_3153, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3149])).
% 5.15/2.06  tff(c_3155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_74, c_72, c_1728, c_3153])).
% 5.15/2.06  tff(c_3156, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_1480])).
% 5.15/2.06  tff(c_4490, plain, (![A_647, B_648, C_649, D_650]: (k3_mcart_1(k5_mcart_1(A_647, B_648, C_649, D_650), k6_mcart_1(A_647, B_648, C_649, D_650), k7_mcart_1(A_647, B_648, C_649, D_650))=D_650 | ~m1_subset_1(D_650, k3_zfmisc_1(A_647, B_648, C_649)) | k1_xboole_0=C_649 | k1_xboole_0=B_648 | k1_xboole_0=A_647)), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.15/2.06  tff(c_4556, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3156, c_4490])).
% 5.15/2.06  tff(c_4560, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4556])).
% 5.15/2.06  tff(c_4562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_74, c_72, c_3464, c_4560])).
% 5.15/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/2.06  
% 5.15/2.06  Inference rules
% 5.15/2.06  ----------------------
% 5.15/2.06  #Ref     : 0
% 5.15/2.06  #Sup     : 1021
% 5.15/2.06  #Fact    : 4
% 5.15/2.06  #Define  : 0
% 5.15/2.06  #Split   : 2
% 5.15/2.06  #Chain   : 0
% 5.15/2.06  #Close   : 0
% 5.15/2.06  
% 5.15/2.06  Ordering : KBO
% 5.15/2.06  
% 5.15/2.06  Simplification rules
% 5.15/2.06  ----------------------
% 5.15/2.06  #Subsume      : 173
% 5.15/2.06  #Demod        : 567
% 5.15/2.06  #Tautology    : 500
% 5.15/2.06  #SimpNegUnit  : 158
% 5.15/2.06  #BackRed      : 4
% 5.15/2.06  
% 5.15/2.06  #Partial instantiations: 0
% 5.15/2.06  #Strategies tried      : 1
% 5.15/2.06  
% 5.15/2.06  Timing (in seconds)
% 5.15/2.06  ----------------------
% 5.15/2.06  Preprocessing        : 0.36
% 5.15/2.06  Parsing              : 0.19
% 5.15/2.06  CNF conversion       : 0.03
% 5.15/2.06  Main loop            : 0.89
% 5.15/2.06  Inferencing          : 0.33
% 5.15/2.06  Reduction            : 0.29
% 5.15/2.06  Demodulation         : 0.19
% 5.15/2.06  BG Simplification    : 0.04
% 5.15/2.06  Subsumption          : 0.15
% 5.15/2.06  Abstraction          : 0.05
% 5.15/2.06  MUC search           : 0.00
% 5.15/2.06  Cooper               : 0.00
% 5.15/2.06  Total                : 1.29
% 5.15/2.06  Index Insertion      : 0.00
% 5.15/2.07  Index Deletion       : 0.00
% 5.15/2.07  Index Matching       : 0.00
% 5.15/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
