%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:41 EST 2020

% Result     : Theorem 5.51s
% Output     : CNFRefutation 5.93s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 208 expanded)
%              Number of leaves         :   41 (  91 expanded)
%              Depth                    :    8
%              Number of atoms          :  187 ( 472 expanded)
%              Number of equality atoms :  148 ( 370 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

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

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_133,axiom,(
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

tff(f_129,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_30,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2235,plain,(
    ! [B_570,A_571] :
      ( ~ r2_hidden(B_570,A_571)
      | k4_xboole_0(A_571,k1_tarski(B_570)) != A_571 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2240,plain,(
    ! [B_570] : ~ r2_hidden(B_570,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2235])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2292,plain,(
    ! [A_578,C_579,B_580] :
      ( r2_hidden(A_578,C_579)
      | k4_xboole_0(k2_tarski(A_578,B_580),C_579) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2303,plain,(
    ! [A_578,B_580] :
      ( r2_hidden(A_578,k1_xboole_0)
      | k2_tarski(A_578,B_580) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2292])).

tff(c_2305,plain,(
    ! [A_581,B_582] : k2_tarski(A_581,B_582) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2240,c_2303])).

tff(c_2307,plain,(
    ! [A_10] : k1_tarski(A_10) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2305])).

tff(c_56,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_3'(A_31),A_31)
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2310,plain,(
    ! [A_584,B_585] :
      ( k4_xboole_0(k1_tarski(A_584),k1_tarski(B_585)) = k1_tarski(A_584)
      | B_585 = A_584 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [B_16,A_15] :
      ( ~ r2_hidden(B_16,A_15)
      | k4_xboole_0(A_15,k1_tarski(B_16)) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2338,plain,(
    ! [B_586,A_587] :
      ( ~ r2_hidden(B_586,k1_tarski(A_587))
      | B_586 = A_587 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2310,c_38])).

tff(c_2345,plain,(
    ! [A_587] :
      ( '#skF_3'(k1_tarski(A_587)) = A_587
      | k1_tarski(A_587) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_2338])).

tff(c_2350,plain,(
    ! [A_587] : '#skF_3'(k1_tarski(A_587)) = A_587 ),
    inference(negUnitSimplification,[status(thm)],[c_2307,c_2345])).

tff(c_145,plain,(
    ! [A_80,B_81] : k1_enumset1(A_80,A_80,B_81) = k2_tarski(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_163,plain,(
    ! [B_82,A_83] : r2_hidden(B_82,k2_tarski(A_83,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_8])).

tff(c_166,plain,(
    ! [A_10] : r2_hidden(A_10,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_163])).

tff(c_2438,plain,(
    ! [D_609,A_610,C_611,E_612] :
      ( ~ r2_hidden(D_609,A_610)
      | k3_mcart_1(C_611,D_609,E_612) != '#skF_3'(A_610)
      | k1_xboole_0 = A_610 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2442,plain,(
    ! [C_611,A_10,E_612] :
      ( k3_mcart_1(C_611,A_10,E_612) != '#skF_3'(k1_tarski(A_10))
      | k1_tarski(A_10) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_166,c_2438])).

tff(c_2457,plain,(
    ! [C_611,A_10,E_612] :
      ( k3_mcart_1(C_611,A_10,E_612) != A_10
      | k1_tarski(A_10) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2350,c_2442])).

tff(c_2458,plain,(
    ! [C_611,A_10,E_612] : k3_mcart_1(C_611,A_10,E_612) != A_10 ),
    inference(negUnitSimplification,[status(thm)],[c_2307,c_2457])).

tff(c_76,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1280,plain,(
    ! [A_347,B_348,C_349] : k4_tarski(k4_tarski(A_347,B_348),C_349) = k3_mcart_1(A_347,B_348,C_349) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_72,plain,(
    ! [A_55,B_56] : k2_mcart_1(k4_tarski(A_55,B_56)) = B_56 ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,(
    ! [B_29,C_30] : k2_mcart_1(k4_tarski(B_29,C_30)) != k4_tarski(B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_84,plain,(
    ! [B_29,C_30] : k4_tarski(B_29,C_30) != C_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_52])).

tff(c_1298,plain,(
    ! [A_347,B_348,C_349] : k3_mcart_1(A_347,B_348,C_349) != C_349 ),
    inference(superposition,[status(thm),theory(equality)],[c_1280,c_84])).

tff(c_204,plain,(
    ! [B_89,A_90] :
      ( ~ r2_hidden(B_89,A_90)
      | k4_xboole_0(A_90,k1_tarski(B_89)) != A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_213,plain,(
    ! [B_89] : ~ r2_hidden(B_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_204])).

tff(c_337,plain,(
    ! [B_115,C_116,A_117] :
      ( r2_hidden(B_115,C_116)
      | k4_xboole_0(k2_tarski(A_117,B_115),C_116) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_348,plain,(
    ! [B_115,A_117] :
      ( r2_hidden(B_115,k1_xboole_0)
      | k2_tarski(A_117,B_115) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_337])).

tff(c_350,plain,(
    ! [A_118,B_119] : k2_tarski(A_118,B_119) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_348])).

tff(c_352,plain,(
    ! [A_10] : k1_tarski(A_10) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_350])).

tff(c_215,plain,(
    ! [A_91,B_92] :
      ( k4_xboole_0(k1_tarski(A_91),k1_tarski(B_92)) = k1_tarski(A_91)
      | B_92 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_250,plain,(
    ! [B_94,A_95] :
      ( ~ r2_hidden(B_94,k1_tarski(A_95))
      | B_94 = A_95 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_38])).

tff(c_260,plain,(
    ! [A_95] :
      ( '#skF_3'(k1_tarski(A_95)) = A_95
      | k1_tarski(A_95) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_250])).

tff(c_353,plain,(
    ! [A_95] : '#skF_3'(k1_tarski(A_95)) = A_95 ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_260])).

tff(c_395,plain,(
    ! [C_127,A_128,D_129,E_130] :
      ( ~ r2_hidden(C_127,A_128)
      | k3_mcart_1(C_127,D_129,E_130) != '#skF_3'(A_128)
      | k1_xboole_0 = A_128 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_399,plain,(
    ! [A_10,D_129,E_130] :
      ( k3_mcart_1(A_10,D_129,E_130) != '#skF_3'(k1_tarski(A_10))
      | k1_tarski(A_10) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_166,c_395])).

tff(c_414,plain,(
    ! [A_10,D_129,E_130] :
      ( k3_mcart_1(A_10,D_129,E_130) != A_10
      | k1_tarski(A_10) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_399])).

tff(c_415,plain,(
    ! [A_10,D_129,E_130] : k3_mcart_1(A_10,D_129,E_130) != A_10 ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_414])).

tff(c_74,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_168,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_879,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( k7_mcart_1(A_231,B_232,C_233,D_234) = k2_mcart_1(D_234)
      | ~ m1_subset_1(D_234,k3_zfmisc_1(A_231,B_232,C_233))
      | k1_xboole_0 = C_233
      | k1_xboole_0 = B_232
      | k1_xboole_0 = A_231 ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_885,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76,c_879])).

tff(c_888,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_885])).

tff(c_1109,plain,(
    ! [A_336,B_337,C_338,D_339] :
      ( k3_mcart_1(k5_mcart_1(A_336,B_337,C_338,D_339),k6_mcart_1(A_336,B_337,C_338,D_339),k7_mcart_1(A_336,B_337,C_338,D_339)) = D_339
      | ~ m1_subset_1(D_339,k3_zfmisc_1(A_336,B_337,C_338))
      | k1_xboole_0 = C_338
      | k1_xboole_0 = B_337
      | k1_xboole_0 = A_336 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1209,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_1109])).

tff(c_1220,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_168,c_1209])).

tff(c_1222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_415,c_1220])).

tff(c_1223,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1231,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1223])).

tff(c_2125,plain,(
    ! [A_566,B_567,C_568,D_569] :
      ( k3_mcart_1(k5_mcart_1(A_566,B_567,C_568,D_569),k6_mcart_1(A_566,B_567,C_568,D_569),k7_mcart_1(A_566,B_567,C_568,D_569)) = D_569
      | ~ m1_subset_1(D_569,k3_zfmisc_1(A_566,B_567,C_568))
      | k1_xboole_0 = C_568
      | k1_xboole_0 = B_567
      | k1_xboole_0 = A_566 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2218,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_2125])).

tff(c_2226,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2218])).

tff(c_2228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_1298,c_2226])).

tff(c_2229,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1223])).

tff(c_2935,plain,(
    ! [A_719,B_720,C_721,D_722] :
      ( k7_mcart_1(A_719,B_720,C_721,D_722) = k2_mcart_1(D_722)
      | ~ m1_subset_1(D_722,k3_zfmisc_1(A_719,B_720,C_721))
      | k1_xboole_0 = C_721
      | k1_xboole_0 = B_720
      | k1_xboole_0 = A_719 ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2941,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76,c_2935])).

tff(c_2944,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_2941])).

tff(c_3447,plain,(
    ! [A_843,B_844,C_845,D_846] :
      ( k3_mcart_1(k5_mcart_1(A_843,B_844,C_845,D_846),k6_mcart_1(A_843,B_844,C_845,D_846),k7_mcart_1(A_843,B_844,C_845,D_846)) = D_846
      | ~ m1_subset_1(D_846,k3_zfmisc_1(A_843,B_844,C_845))
      | k1_xboole_0 = C_845
      | k1_xboole_0 = B_844
      | k1_xboole_0 = A_843 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3556,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2944,c_3447])).

tff(c_3567,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2229,c_3556])).

tff(c_3569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80,c_78,c_2458,c_3567])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:41:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.51/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.20  
% 5.51/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.51/2.20  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 5.51/2.20  
% 5.51/2.20  %Foreground sorts:
% 5.51/2.20  
% 5.51/2.20  
% 5.51/2.20  %Background operators:
% 5.51/2.20  
% 5.51/2.20  
% 5.51/2.20  %Foreground operators:
% 5.51/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.51/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.51/2.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.51/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.51/2.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.51/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.51/2.20  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.51/2.20  tff('#skF_7', type, '#skF_7': $i).
% 5.51/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.51/2.20  tff('#skF_5', type, '#skF_5': $i).
% 5.51/2.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.51/2.20  tff('#skF_6', type, '#skF_6': $i).
% 5.51/2.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.51/2.20  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 5.51/2.20  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.51/2.20  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 5.51/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.51/2.20  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.51/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.51/2.20  tff('#skF_4', type, '#skF_4': $i).
% 5.51/2.20  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.51/2.20  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 5.51/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.51/2.20  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.51/2.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.51/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.51/2.20  
% 5.93/2.22  tff(f_157, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 5.93/2.22  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.93/2.22  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 5.93/2.22  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.93/2.22  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.93/2.22  tff(f_64, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 5.93/2.22  tff(f_93, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 5.93/2.22  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 5.93/2.22  tff(f_48, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.93/2.22  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.93/2.22  tff(f_66, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 5.93/2.22  tff(f_133, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 5.93/2.22  tff(f_77, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 5.93/2.22  tff(f_129, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 5.93/2.22  tff(f_109, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 5.93/2.22  tff(c_82, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.93/2.22  tff(c_80, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.93/2.22  tff(c_78, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.93/2.22  tff(c_30, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.93/2.22  tff(c_4, plain, (![A_2]: (k4_xboole_0(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.93/2.22  tff(c_2235, plain, (![B_570, A_571]: (~r2_hidden(B_570, A_571) | k4_xboole_0(A_571, k1_tarski(B_570))!=A_571)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.93/2.22  tff(c_2240, plain, (![B_570]: (~r2_hidden(B_570, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2235])).
% 5.93/2.22  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.93/2.22  tff(c_2292, plain, (![A_578, C_579, B_580]: (r2_hidden(A_578, C_579) | k4_xboole_0(k2_tarski(A_578, B_580), C_579)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.93/2.22  tff(c_2303, plain, (![A_578, B_580]: (r2_hidden(A_578, k1_xboole_0) | k2_tarski(A_578, B_580)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2292])).
% 5.93/2.22  tff(c_2305, plain, (![A_581, B_582]: (k2_tarski(A_581, B_582)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_2240, c_2303])).
% 5.93/2.22  tff(c_2307, plain, (![A_10]: (k1_tarski(A_10)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_2305])).
% 5.93/2.22  tff(c_56, plain, (![A_31]: (r2_hidden('#skF_3'(A_31), A_31) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.93/2.22  tff(c_2310, plain, (![A_584, B_585]: (k4_xboole_0(k1_tarski(A_584), k1_tarski(B_585))=k1_tarski(A_584) | B_585=A_584)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.93/2.22  tff(c_38, plain, (![B_16, A_15]: (~r2_hidden(B_16, A_15) | k4_xboole_0(A_15, k1_tarski(B_16))!=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.93/2.22  tff(c_2338, plain, (![B_586, A_587]: (~r2_hidden(B_586, k1_tarski(A_587)) | B_586=A_587)), inference(superposition, [status(thm), theory('equality')], [c_2310, c_38])).
% 5.93/2.22  tff(c_2345, plain, (![A_587]: ('#skF_3'(k1_tarski(A_587))=A_587 | k1_tarski(A_587)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_2338])).
% 5.93/2.22  tff(c_2350, plain, (![A_587]: ('#skF_3'(k1_tarski(A_587))=A_587)), inference(negUnitSimplification, [status(thm)], [c_2307, c_2345])).
% 5.93/2.22  tff(c_145, plain, (![A_80, B_81]: (k1_enumset1(A_80, A_80, B_81)=k2_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.93/2.22  tff(c_8, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.93/2.22  tff(c_163, plain, (![B_82, A_83]: (r2_hidden(B_82, k2_tarski(A_83, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_8])).
% 5.93/2.22  tff(c_166, plain, (![A_10]: (r2_hidden(A_10, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_163])).
% 5.93/2.22  tff(c_2438, plain, (![D_609, A_610, C_611, E_612]: (~r2_hidden(D_609, A_610) | k3_mcart_1(C_611, D_609, E_612)!='#skF_3'(A_610) | k1_xboole_0=A_610)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.93/2.22  tff(c_2442, plain, (![C_611, A_10, E_612]: (k3_mcart_1(C_611, A_10, E_612)!='#skF_3'(k1_tarski(A_10)) | k1_tarski(A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_166, c_2438])).
% 5.93/2.22  tff(c_2457, plain, (![C_611, A_10, E_612]: (k3_mcart_1(C_611, A_10, E_612)!=A_10 | k1_tarski(A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2350, c_2442])).
% 5.93/2.22  tff(c_2458, plain, (![C_611, A_10, E_612]: (k3_mcart_1(C_611, A_10, E_612)!=A_10)), inference(negUnitSimplification, [status(thm)], [c_2307, c_2457])).
% 5.93/2.22  tff(c_76, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.93/2.22  tff(c_1280, plain, (![A_347, B_348, C_349]: (k4_tarski(k4_tarski(A_347, B_348), C_349)=k3_mcart_1(A_347, B_348, C_349))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.93/2.22  tff(c_72, plain, (![A_55, B_56]: (k2_mcart_1(k4_tarski(A_55, B_56))=B_56)), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.93/2.22  tff(c_52, plain, (![B_29, C_30]: (k2_mcart_1(k4_tarski(B_29, C_30))!=k4_tarski(B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.93/2.22  tff(c_84, plain, (![B_29, C_30]: (k4_tarski(B_29, C_30)!=C_30)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_52])).
% 5.93/2.22  tff(c_1298, plain, (![A_347, B_348, C_349]: (k3_mcart_1(A_347, B_348, C_349)!=C_349)), inference(superposition, [status(thm), theory('equality')], [c_1280, c_84])).
% 5.93/2.22  tff(c_204, plain, (![B_89, A_90]: (~r2_hidden(B_89, A_90) | k4_xboole_0(A_90, k1_tarski(B_89))!=A_90)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.93/2.22  tff(c_213, plain, (![B_89]: (~r2_hidden(B_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_204])).
% 5.93/2.22  tff(c_337, plain, (![B_115, C_116, A_117]: (r2_hidden(B_115, C_116) | k4_xboole_0(k2_tarski(A_117, B_115), C_116)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.93/2.22  tff(c_348, plain, (![B_115, A_117]: (r2_hidden(B_115, k1_xboole_0) | k2_tarski(A_117, B_115)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_337])).
% 5.93/2.22  tff(c_350, plain, (![A_118, B_119]: (k2_tarski(A_118, B_119)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_213, c_348])).
% 5.93/2.22  tff(c_352, plain, (![A_10]: (k1_tarski(A_10)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_350])).
% 5.93/2.22  tff(c_215, plain, (![A_91, B_92]: (k4_xboole_0(k1_tarski(A_91), k1_tarski(B_92))=k1_tarski(A_91) | B_92=A_91)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.93/2.22  tff(c_250, plain, (![B_94, A_95]: (~r2_hidden(B_94, k1_tarski(A_95)) | B_94=A_95)), inference(superposition, [status(thm), theory('equality')], [c_215, c_38])).
% 5.93/2.22  tff(c_260, plain, (![A_95]: ('#skF_3'(k1_tarski(A_95))=A_95 | k1_tarski(A_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_250])).
% 5.93/2.22  tff(c_353, plain, (![A_95]: ('#skF_3'(k1_tarski(A_95))=A_95)), inference(negUnitSimplification, [status(thm)], [c_352, c_260])).
% 5.93/2.22  tff(c_395, plain, (![C_127, A_128, D_129, E_130]: (~r2_hidden(C_127, A_128) | k3_mcart_1(C_127, D_129, E_130)!='#skF_3'(A_128) | k1_xboole_0=A_128)), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.93/2.22  tff(c_399, plain, (![A_10, D_129, E_130]: (k3_mcart_1(A_10, D_129, E_130)!='#skF_3'(k1_tarski(A_10)) | k1_tarski(A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_166, c_395])).
% 5.93/2.22  tff(c_414, plain, (![A_10, D_129, E_130]: (k3_mcart_1(A_10, D_129, E_130)!=A_10 | k1_tarski(A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_353, c_399])).
% 5.93/2.22  tff(c_415, plain, (![A_10, D_129, E_130]: (k3_mcart_1(A_10, D_129, E_130)!=A_10)), inference(negUnitSimplification, [status(thm)], [c_352, c_414])).
% 5.93/2.22  tff(c_74, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.93/2.22  tff(c_168, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_74])).
% 5.93/2.22  tff(c_879, plain, (![A_231, B_232, C_233, D_234]: (k7_mcart_1(A_231, B_232, C_233, D_234)=k2_mcart_1(D_234) | ~m1_subset_1(D_234, k3_zfmisc_1(A_231, B_232, C_233)) | k1_xboole_0=C_233 | k1_xboole_0=B_232 | k1_xboole_0=A_231)), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.93/2.22  tff(c_885, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_76, c_879])).
% 5.93/2.22  tff(c_888, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_885])).
% 5.93/2.22  tff(c_1109, plain, (![A_336, B_337, C_338, D_339]: (k3_mcart_1(k5_mcart_1(A_336, B_337, C_338, D_339), k6_mcart_1(A_336, B_337, C_338, D_339), k7_mcart_1(A_336, B_337, C_338, D_339))=D_339 | ~m1_subset_1(D_339, k3_zfmisc_1(A_336, B_337, C_338)) | k1_xboole_0=C_338 | k1_xboole_0=B_337 | k1_xboole_0=A_336)), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.93/2.22  tff(c_1209, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_888, c_1109])).
% 5.93/2.22  tff(c_1220, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_168, c_1209])).
% 5.93/2.22  tff(c_1222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_415, c_1220])).
% 5.93/2.22  tff(c_1223, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 5.93/2.22  tff(c_1231, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_1223])).
% 5.93/2.22  tff(c_2125, plain, (![A_566, B_567, C_568, D_569]: (k3_mcart_1(k5_mcart_1(A_566, B_567, C_568, D_569), k6_mcart_1(A_566, B_567, C_568, D_569), k7_mcart_1(A_566, B_567, C_568, D_569))=D_569 | ~m1_subset_1(D_569, k3_zfmisc_1(A_566, B_567, C_568)) | k1_xboole_0=C_568 | k1_xboole_0=B_567 | k1_xboole_0=A_566)), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.93/2.22  tff(c_2218, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1231, c_2125])).
% 5.93/2.22  tff(c_2226, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2218])).
% 5.93/2.22  tff(c_2228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_1298, c_2226])).
% 5.93/2.22  tff(c_2229, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_1223])).
% 5.93/2.22  tff(c_2935, plain, (![A_719, B_720, C_721, D_722]: (k7_mcart_1(A_719, B_720, C_721, D_722)=k2_mcart_1(D_722) | ~m1_subset_1(D_722, k3_zfmisc_1(A_719, B_720, C_721)) | k1_xboole_0=C_721 | k1_xboole_0=B_720 | k1_xboole_0=A_719)), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.93/2.22  tff(c_2941, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_76, c_2935])).
% 5.93/2.22  tff(c_2944, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_2941])).
% 5.93/2.22  tff(c_3447, plain, (![A_843, B_844, C_845, D_846]: (k3_mcart_1(k5_mcart_1(A_843, B_844, C_845, D_846), k6_mcart_1(A_843, B_844, C_845, D_846), k7_mcart_1(A_843, B_844, C_845, D_846))=D_846 | ~m1_subset_1(D_846, k3_zfmisc_1(A_843, B_844, C_845)) | k1_xboole_0=C_845 | k1_xboole_0=B_844 | k1_xboole_0=A_843)), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.93/2.22  tff(c_3556, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2944, c_3447])).
% 5.93/2.22  tff(c_3567, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2229, c_3556])).
% 5.93/2.22  tff(c_3569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80, c_78, c_2458, c_3567])).
% 5.93/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.22  
% 5.93/2.22  Inference rules
% 5.93/2.22  ----------------------
% 5.93/2.22  #Ref     : 22
% 5.93/2.22  #Sup     : 801
% 5.93/2.22  #Fact    : 12
% 5.93/2.22  #Define  : 0
% 5.93/2.22  #Split   : 2
% 5.93/2.22  #Chain   : 0
% 5.93/2.22  #Close   : 0
% 5.93/2.22  
% 5.93/2.22  Ordering : KBO
% 5.93/2.22  
% 5.93/2.22  Simplification rules
% 5.93/2.22  ----------------------
% 5.93/2.22  #Subsume      : 250
% 5.93/2.22  #Demod        : 303
% 5.93/2.22  #Tautology    : 262
% 5.93/2.22  #SimpNegUnit  : 126
% 5.93/2.22  #BackRed      : 2
% 5.93/2.22  
% 5.93/2.22  #Partial instantiations: 0
% 5.93/2.22  #Strategies tried      : 1
% 5.93/2.22  
% 5.93/2.22  Timing (in seconds)
% 5.93/2.22  ----------------------
% 5.93/2.23  Preprocessing        : 0.43
% 5.93/2.23  Parsing              : 0.21
% 5.93/2.23  CNF conversion       : 0.03
% 5.93/2.23  Main loop            : 0.94
% 5.93/2.23  Inferencing          : 0.36
% 5.93/2.23  Reduction            : 0.30
% 5.93/2.23  Demodulation         : 0.19
% 5.93/2.23  BG Simplification    : 0.05
% 5.93/2.23  Subsumption          : 0.17
% 5.93/2.23  Abstraction          : 0.06
% 5.93/2.23  MUC search           : 0.00
% 5.93/2.23  Cooper               : 0.00
% 5.93/2.23  Total                : 1.41
% 5.93/2.23  Index Insertion      : 0.00
% 5.93/2.23  Index Deletion       : 0.00
% 5.93/2.23  Index Matching       : 0.00
% 5.93/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
