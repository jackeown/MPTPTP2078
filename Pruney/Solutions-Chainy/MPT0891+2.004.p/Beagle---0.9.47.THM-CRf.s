%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:40 EST 2020

% Result     : Theorem 7.60s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 260 expanded)
%              Number of leaves         :   43 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  195 ( 641 expanded)
%              Number of equality atoms :  144 ( 428 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_98,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_71,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_134,axiom,(
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

tff(f_114,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,(
    ! [A_85,B_86] : k1_enumset1(A_85,A_85,B_86) = k2_tarski(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [E_13,A_7,C_9] : r2_hidden(E_13,k1_enumset1(A_7,E_13,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_154,plain,(
    ! [A_85,B_86] : r2_hidden(A_85,k2_tarski(A_85,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_24])).

tff(c_74,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_7'(A_36),A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3849,plain,(
    ! [D_475,A_476,B_477] :
      ( r2_hidden(D_475,A_476)
      | ~ r2_hidden(D_475,k4_xboole_0(A_476,B_477)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3854,plain,(
    ! [A_476,B_477] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_476,B_477)),A_476)
      | k4_xboole_0(A_476,B_477) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_3849])).

tff(c_3855,plain,(
    ! [D_478,B_479,A_480] :
      ( ~ r2_hidden(D_478,B_479)
      | ~ r2_hidden(D_478,k4_xboole_0(A_480,B_479)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6803,plain,(
    ! [A_821,B_822] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_821,B_822)),B_822)
      | k4_xboole_0(A_821,B_822) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_3855])).

tff(c_6808,plain,(
    ! [A_476] : k4_xboole_0(A_476,A_476) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3854,c_6803])).

tff(c_6892,plain,(
    ! [A_831,C_832,B_833] :
      ( ~ r2_hidden(A_831,C_832)
      | k4_xboole_0(k2_tarski(A_831,B_833),C_832) != k2_tarski(A_831,B_833) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6896,plain,(
    ! [A_831,B_833] :
      ( ~ r2_hidden(A_831,k2_tarski(A_831,B_833))
      | k2_tarski(A_831,B_833) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6808,c_6892])).

tff(c_6924,plain,(
    ! [A_837,B_838] : k2_tarski(A_837,B_838) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_6896])).

tff(c_6926,plain,(
    ! [A_19] : k1_tarski(A_19) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_6924])).

tff(c_141,plain,(
    ! [A_81] :
      ( r2_hidden('#skF_7'(A_81),A_81)
      | k1_xboole_0 = A_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_146,plain,(
    ! [A_14] :
      ( '#skF_7'(k1_tarski(A_14)) = A_14
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_141,c_44])).

tff(c_6927,plain,(
    ! [A_14] : '#skF_7'(k1_tarski(A_14)) = A_14 ),
    inference(negUnitSimplification,[status(thm)],[c_6926,c_146])).

tff(c_6809,plain,(
    ! [D_823,A_824,C_825,E_826] :
      ( ~ r2_hidden(D_823,A_824)
      | k3_mcart_1(C_825,D_823,E_826) != '#skF_7'(A_824)
      | k1_xboole_0 = A_824 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6996,plain,(
    ! [C_847,A_848,E_849] :
      ( k3_mcart_1(C_847,'#skF_7'(A_848),E_849) != '#skF_7'(A_848)
      | k1_xboole_0 = A_848 ) ),
    inference(resolution,[status(thm)],[c_74,c_6809])).

tff(c_6999,plain,(
    ! [C_847,A_14,E_849] :
      ( k3_mcart_1(C_847,A_14,E_849) != '#skF_7'(k1_tarski(A_14))
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6927,c_6996])).

tff(c_7000,plain,(
    ! [C_847,A_14,E_849] :
      ( k3_mcart_1(C_847,A_14,E_849) != A_14
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6927,c_6999])).

tff(c_7001,plain,(
    ! [C_847,A_14,E_849] : k3_mcart_1(C_847,A_14,E_849) != A_14 ),
    inference(negUnitSimplification,[status(thm)],[c_6926,c_7000])).

tff(c_94,plain,(
    m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3861,plain,(
    ! [A_481,B_482,C_483] : k4_tarski(k4_tarski(A_481,B_482),C_483) = k3_mcart_1(A_481,B_482,C_483) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_90,plain,(
    ! [A_60,B_61] : k2_mcart_1(k4_tarski(A_60,B_61)) = B_61 ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_70,plain,(
    ! [B_34,C_35] : k2_mcart_1(k4_tarski(B_34,C_35)) != k4_tarski(B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_102,plain,(
    ! [B_34,C_35] : k4_tarski(B_34,C_35) != C_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_70])).

tff(c_3879,plain,(
    ! [A_481,B_482,C_483] : k3_mcart_1(A_481,B_482,C_483) != C_483 ),
    inference(superposition,[status(thm),theory(equality)],[c_3861,c_102])).

tff(c_46,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_196,plain,(
    ! [D_92,A_93,B_94] :
      ( r2_hidden(D_92,A_93)
      | ~ r2_hidden(D_92,k4_xboole_0(A_93,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_277,plain,(
    ! [A_123,B_124] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_123,B_124)),A_123)
      | k4_xboole_0(A_123,B_124) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_196])).

tff(c_202,plain,(
    ! [D_95,B_96,A_97] :
      ( ~ r2_hidden(D_95,B_96)
      | ~ r2_hidden(D_95,k4_xboole_0(A_97,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_207,plain,(
    ! [A_97,B_96] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_97,B_96)),B_96)
      | k4_xboole_0(A_97,B_96) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_202])).

tff(c_298,plain,(
    ! [A_125] : k4_xboole_0(A_125,A_125) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_277,c_207])).

tff(c_261,plain,(
    ! [B_113,C_114,A_115] :
      ( ~ r2_hidden(B_113,C_114)
      | k4_xboole_0(k2_tarski(A_115,B_113),C_114) != k2_tarski(A_115,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_264,plain,(
    ! [A_19,C_114] :
      ( ~ r2_hidden(A_19,C_114)
      | k4_xboole_0(k1_tarski(A_19),C_114) != k2_tarski(A_19,A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_261])).

tff(c_265,plain,(
    ! [A_19,C_114] :
      ( ~ r2_hidden(A_19,C_114)
      | k4_xboole_0(k1_tarski(A_19),C_114) != k1_tarski(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_264])).

tff(c_310,plain,(
    ! [A_19] :
      ( ~ r2_hidden(A_19,k1_tarski(A_19))
      | k1_tarski(A_19) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_265])).

tff(c_327,plain,(
    ! [A_19] : k1_tarski(A_19) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_310])).

tff(c_356,plain,(
    ! [A_14] : '#skF_7'(k1_tarski(A_14)) = A_14 ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_146])).

tff(c_489,plain,(
    ! [C_152,A_153,D_154,E_155] :
      ( ~ r2_hidden(C_152,A_153)
      | k3_mcart_1(C_152,D_154,E_155) != '#skF_7'(A_153)
      | k1_xboole_0 = A_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_507,plain,(
    ! [C_18,D_154,E_155] :
      ( k3_mcart_1(C_18,D_154,E_155) != '#skF_7'(k1_tarski(C_18))
      | k1_tarski(C_18) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_489])).

tff(c_521,plain,(
    ! [C_18,D_154,E_155] :
      ( k3_mcart_1(C_18,D_154,E_155) != C_18
      | k1_tarski(C_18) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_507])).

tff(c_522,plain,(
    ! [C_18,D_154,E_155] : k3_mcart_1(C_18,D_154,E_155) != C_18 ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_521])).

tff(c_92,plain,
    ( k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11'
    | k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11'
    | k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_177,plain,(
    k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_1592,plain,(
    ! [A_316,B_317,C_318,D_319] :
      ( k7_mcart_1(A_316,B_317,C_318,D_319) = k2_mcart_1(D_319)
      | ~ m1_subset_1(D_319,k3_zfmisc_1(A_316,B_317,C_318))
      | k1_xboole_0 = C_318
      | k1_xboole_0 = B_317
      | k1_xboole_0 = A_316 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1598,plain,
    ( k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11')
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_94,c_1592])).

tff(c_1601,plain,(
    k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_1598])).

tff(c_3732,plain,(
    ! [A_470,B_471,C_472,D_473] :
      ( k3_mcart_1(k5_mcart_1(A_470,B_471,C_472,D_473),k6_mcart_1(A_470,B_471,C_472,D_473),k7_mcart_1(A_470,B_471,C_472,D_473)) = D_473
      | ~ m1_subset_1(D_473,k3_zfmisc_1(A_470,B_471,C_472))
      | k1_xboole_0 = C_472
      | k1_xboole_0 = B_471
      | k1_xboole_0 = A_470 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3819,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k2_mcart_1('#skF_11')) = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1601,c_3732])).

tff(c_3830,plain,
    ( k3_mcart_1('#skF_11',k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k2_mcart_1('#skF_11')) = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_177,c_3819])).

tff(c_3832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_522,c_3830])).

tff(c_3833,plain,
    ( k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11'
    | k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_3914,plain,(
    k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_3833])).

tff(c_6677,plain,(
    ! [A_812,B_813,C_814,D_815] :
      ( k3_mcart_1(k5_mcart_1(A_812,B_813,C_814,D_815),k6_mcart_1(A_812,B_813,C_814,D_815),k7_mcart_1(A_812,B_813,C_814,D_815)) = D_815
      | ~ m1_subset_1(D_815,k3_zfmisc_1(A_812,B_813,C_814))
      | k1_xboole_0 = C_814
      | k1_xboole_0 = B_813
      | k1_xboole_0 = A_812 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6761,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),'#skF_11') = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_3914,c_6677])).

tff(c_6769,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),'#skF_11') = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_6761])).

tff(c_6771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_3879,c_6769])).

tff(c_6772,plain,(
    k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_3833])).

tff(c_8197,plain,(
    ! [A_1025,B_1026,C_1027,D_1028] :
      ( k7_mcart_1(A_1025,B_1026,C_1027,D_1028) = k2_mcart_1(D_1028)
      | ~ m1_subset_1(D_1028,k3_zfmisc_1(A_1025,B_1026,C_1027))
      | k1_xboole_0 = C_1027
      | k1_xboole_0 = B_1026
      | k1_xboole_0 = A_1025 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8203,plain,
    ( k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11')
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_94,c_8197])).

tff(c_8206,plain,(
    k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_8203])).

tff(c_10321,plain,(
    ! [A_1176,B_1177,C_1178,D_1179] :
      ( k3_mcart_1(k5_mcart_1(A_1176,B_1177,C_1178,D_1179),k6_mcart_1(A_1176,B_1177,C_1178,D_1179),k7_mcart_1(A_1176,B_1177,C_1178,D_1179)) = D_1179
      | ~ m1_subset_1(D_1179,k3_zfmisc_1(A_1176,B_1177,C_1178))
      | k1_xboole_0 = C_1178
      | k1_xboole_0 = B_1177
      | k1_xboole_0 = A_1176 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10408,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k2_mcart_1('#skF_11')) = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_8206,c_10321])).

tff(c_10419,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),'#skF_11',k2_mcart_1('#skF_11')) = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_6772,c_10408])).

tff(c_10421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_98,c_96,c_7001,c_10419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:15:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.60/2.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.79  
% 7.60/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.79  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 7.60/2.79  
% 7.60/2.79  %Foreground sorts:
% 7.60/2.79  
% 7.60/2.79  
% 7.60/2.79  %Background operators:
% 7.60/2.79  
% 7.60/2.79  
% 7.60/2.79  %Foreground operators:
% 7.60/2.79  tff('#skF_7', type, '#skF_7': $i > $i).
% 7.60/2.79  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.60/2.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.60/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.60/2.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.60/2.79  tff('#skF_11', type, '#skF_11': $i).
% 7.60/2.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.60/2.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.60/2.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.60/2.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.60/2.79  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.60/2.79  tff('#skF_10', type, '#skF_10': $i).
% 7.60/2.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.60/2.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.60/2.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.60/2.79  tff('#skF_9', type, '#skF_9': $i).
% 7.60/2.79  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 7.60/2.79  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.60/2.79  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.60/2.79  tff('#skF_8', type, '#skF_8': $i).
% 7.60/2.79  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 7.60/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.60/2.79  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.60/2.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.60/2.79  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 7.60/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.60/2.79  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.60/2.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.60/2.79  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.60/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.60/2.79  
% 7.60/2.81  tff(f_162, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 7.60/2.81  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.60/2.81  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.60/2.81  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.60/2.81  tff(f_98, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 7.60/2.81  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.60/2.81  tff(f_69, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 7.60/2.81  tff(f_57, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 7.60/2.81  tff(f_71, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 7.60/2.81  tff(f_138, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 7.60/2.81  tff(f_82, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 7.60/2.81  tff(f_134, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 7.60/2.81  tff(f_114, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 7.60/2.81  tff(c_100, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.60/2.81  tff(c_98, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.60/2.81  tff(c_96, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.60/2.81  tff(c_56, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.60/2.81  tff(c_148, plain, (![A_85, B_86]: (k1_enumset1(A_85, A_85, B_86)=k2_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.60/2.81  tff(c_24, plain, (![E_13, A_7, C_9]: (r2_hidden(E_13, k1_enumset1(A_7, E_13, C_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.60/2.81  tff(c_154, plain, (![A_85, B_86]: (r2_hidden(A_85, k2_tarski(A_85, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_148, c_24])).
% 7.60/2.81  tff(c_74, plain, (![A_36]: (r2_hidden('#skF_7'(A_36), A_36) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.60/2.81  tff(c_3849, plain, (![D_475, A_476, B_477]: (r2_hidden(D_475, A_476) | ~r2_hidden(D_475, k4_xboole_0(A_476, B_477)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.60/2.81  tff(c_3854, plain, (![A_476, B_477]: (r2_hidden('#skF_7'(k4_xboole_0(A_476, B_477)), A_476) | k4_xboole_0(A_476, B_477)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_3849])).
% 7.60/2.81  tff(c_3855, plain, (![D_478, B_479, A_480]: (~r2_hidden(D_478, B_479) | ~r2_hidden(D_478, k4_xboole_0(A_480, B_479)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.60/2.81  tff(c_6803, plain, (![A_821, B_822]: (~r2_hidden('#skF_7'(k4_xboole_0(A_821, B_822)), B_822) | k4_xboole_0(A_821, B_822)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_3855])).
% 7.60/2.81  tff(c_6808, plain, (![A_476]: (k4_xboole_0(A_476, A_476)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3854, c_6803])).
% 7.60/2.81  tff(c_6892, plain, (![A_831, C_832, B_833]: (~r2_hidden(A_831, C_832) | k4_xboole_0(k2_tarski(A_831, B_833), C_832)!=k2_tarski(A_831, B_833))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.60/2.81  tff(c_6896, plain, (![A_831, B_833]: (~r2_hidden(A_831, k2_tarski(A_831, B_833)) | k2_tarski(A_831, B_833)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6808, c_6892])).
% 7.60/2.81  tff(c_6924, plain, (![A_837, B_838]: (k2_tarski(A_837, B_838)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_6896])).
% 7.60/2.81  tff(c_6926, plain, (![A_19]: (k1_tarski(A_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_6924])).
% 7.60/2.81  tff(c_141, plain, (![A_81]: (r2_hidden('#skF_7'(A_81), A_81) | k1_xboole_0=A_81)), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.60/2.81  tff(c_44, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.60/2.81  tff(c_146, plain, (![A_14]: ('#skF_7'(k1_tarski(A_14))=A_14 | k1_tarski(A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_141, c_44])).
% 7.60/2.81  tff(c_6927, plain, (![A_14]: ('#skF_7'(k1_tarski(A_14))=A_14)), inference(negUnitSimplification, [status(thm)], [c_6926, c_146])).
% 7.60/2.81  tff(c_6809, plain, (![D_823, A_824, C_825, E_826]: (~r2_hidden(D_823, A_824) | k3_mcart_1(C_825, D_823, E_826)!='#skF_7'(A_824) | k1_xboole_0=A_824)), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.60/2.81  tff(c_6996, plain, (![C_847, A_848, E_849]: (k3_mcart_1(C_847, '#skF_7'(A_848), E_849)!='#skF_7'(A_848) | k1_xboole_0=A_848)), inference(resolution, [status(thm)], [c_74, c_6809])).
% 7.60/2.81  tff(c_6999, plain, (![C_847, A_14, E_849]: (k3_mcart_1(C_847, A_14, E_849)!='#skF_7'(k1_tarski(A_14)) | k1_tarski(A_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6927, c_6996])).
% 7.60/2.81  tff(c_7000, plain, (![C_847, A_14, E_849]: (k3_mcart_1(C_847, A_14, E_849)!=A_14 | k1_tarski(A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6927, c_6999])).
% 7.60/2.81  tff(c_7001, plain, (![C_847, A_14, E_849]: (k3_mcart_1(C_847, A_14, E_849)!=A_14)), inference(negUnitSimplification, [status(thm)], [c_6926, c_7000])).
% 7.60/2.81  tff(c_94, plain, (m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.60/2.81  tff(c_3861, plain, (![A_481, B_482, C_483]: (k4_tarski(k4_tarski(A_481, B_482), C_483)=k3_mcart_1(A_481, B_482, C_483))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.60/2.81  tff(c_90, plain, (![A_60, B_61]: (k2_mcart_1(k4_tarski(A_60, B_61))=B_61)), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.60/2.81  tff(c_70, plain, (![B_34, C_35]: (k2_mcart_1(k4_tarski(B_34, C_35))!=k4_tarski(B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.60/2.81  tff(c_102, plain, (![B_34, C_35]: (k4_tarski(B_34, C_35)!=C_35)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_70])).
% 7.60/2.81  tff(c_3879, plain, (![A_481, B_482, C_483]: (k3_mcart_1(A_481, B_482, C_483)!=C_483)), inference(superposition, [status(thm), theory('equality')], [c_3861, c_102])).
% 7.60/2.81  tff(c_46, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.60/2.81  tff(c_196, plain, (![D_92, A_93, B_94]: (r2_hidden(D_92, A_93) | ~r2_hidden(D_92, k4_xboole_0(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.60/2.81  tff(c_277, plain, (![A_123, B_124]: (r2_hidden('#skF_7'(k4_xboole_0(A_123, B_124)), A_123) | k4_xboole_0(A_123, B_124)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_196])).
% 7.60/2.81  tff(c_202, plain, (![D_95, B_96, A_97]: (~r2_hidden(D_95, B_96) | ~r2_hidden(D_95, k4_xboole_0(A_97, B_96)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.60/2.81  tff(c_207, plain, (![A_97, B_96]: (~r2_hidden('#skF_7'(k4_xboole_0(A_97, B_96)), B_96) | k4_xboole_0(A_97, B_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_202])).
% 7.60/2.81  tff(c_298, plain, (![A_125]: (k4_xboole_0(A_125, A_125)=k1_xboole_0)), inference(resolution, [status(thm)], [c_277, c_207])).
% 7.60/2.81  tff(c_261, plain, (![B_113, C_114, A_115]: (~r2_hidden(B_113, C_114) | k4_xboole_0(k2_tarski(A_115, B_113), C_114)!=k2_tarski(A_115, B_113))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.60/2.81  tff(c_264, plain, (![A_19, C_114]: (~r2_hidden(A_19, C_114) | k4_xboole_0(k1_tarski(A_19), C_114)!=k2_tarski(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_56, c_261])).
% 7.60/2.81  tff(c_265, plain, (![A_19, C_114]: (~r2_hidden(A_19, C_114) | k4_xboole_0(k1_tarski(A_19), C_114)!=k1_tarski(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_264])).
% 7.60/2.81  tff(c_310, plain, (![A_19]: (~r2_hidden(A_19, k1_tarski(A_19)) | k1_tarski(A_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_298, c_265])).
% 7.60/2.81  tff(c_327, plain, (![A_19]: (k1_tarski(A_19)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_310])).
% 7.60/2.81  tff(c_356, plain, (![A_14]: ('#skF_7'(k1_tarski(A_14))=A_14)), inference(negUnitSimplification, [status(thm)], [c_327, c_146])).
% 7.60/2.81  tff(c_489, plain, (![C_152, A_153, D_154, E_155]: (~r2_hidden(C_152, A_153) | k3_mcart_1(C_152, D_154, E_155)!='#skF_7'(A_153) | k1_xboole_0=A_153)), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.60/2.81  tff(c_507, plain, (![C_18, D_154, E_155]: (k3_mcart_1(C_18, D_154, E_155)!='#skF_7'(k1_tarski(C_18)) | k1_tarski(C_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_489])).
% 7.60/2.81  tff(c_521, plain, (![C_18, D_154, E_155]: (k3_mcart_1(C_18, D_154, E_155)!=C_18 | k1_tarski(C_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_356, c_507])).
% 7.60/2.81  tff(c_522, plain, (![C_18, D_154, E_155]: (k3_mcart_1(C_18, D_154, E_155)!=C_18)), inference(negUnitSimplification, [status(thm)], [c_327, c_521])).
% 7.60/2.81  tff(c_92, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11' | k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11' | k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.60/2.81  tff(c_177, plain, (k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitLeft, [status(thm)], [c_92])).
% 7.60/2.81  tff(c_1592, plain, (![A_316, B_317, C_318, D_319]: (k7_mcart_1(A_316, B_317, C_318, D_319)=k2_mcart_1(D_319) | ~m1_subset_1(D_319, k3_zfmisc_1(A_316, B_317, C_318)) | k1_xboole_0=C_318 | k1_xboole_0=B_317 | k1_xboole_0=A_316)), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.60/2.81  tff(c_1598, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11') | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_94, c_1592])).
% 7.60/2.81  tff(c_1601, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_1598])).
% 7.60/2.81  tff(c_3732, plain, (![A_470, B_471, C_472, D_473]: (k3_mcart_1(k5_mcart_1(A_470, B_471, C_472, D_473), k6_mcart_1(A_470, B_471, C_472, D_473), k7_mcart_1(A_470, B_471, C_472, D_473))=D_473 | ~m1_subset_1(D_473, k3_zfmisc_1(A_470, B_471, C_472)) | k1_xboole_0=C_472 | k1_xboole_0=B_471 | k1_xboole_0=A_470)), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.60/2.81  tff(c_3819, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k2_mcart_1('#skF_11'))='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1601, c_3732])).
% 7.60/2.81  tff(c_3830, plain, (k3_mcart_1('#skF_11', k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k2_mcart_1('#skF_11'))='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_177, c_3819])).
% 7.60/2.81  tff(c_3832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_522, c_3830])).
% 7.60/2.81  tff(c_3833, plain, (k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11' | k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitRight, [status(thm)], [c_92])).
% 7.60/2.81  tff(c_3914, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitLeft, [status(thm)], [c_3833])).
% 7.60/2.81  tff(c_6677, plain, (![A_812, B_813, C_814, D_815]: (k3_mcart_1(k5_mcart_1(A_812, B_813, C_814, D_815), k6_mcart_1(A_812, B_813, C_814, D_815), k7_mcart_1(A_812, B_813, C_814, D_815))=D_815 | ~m1_subset_1(D_815, k3_zfmisc_1(A_812, B_813, C_814)) | k1_xboole_0=C_814 | k1_xboole_0=B_813 | k1_xboole_0=A_812)), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.60/2.81  tff(c_6761, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), '#skF_11')='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_3914, c_6677])).
% 7.60/2.81  tff(c_6769, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), '#skF_11')='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_6761])).
% 7.60/2.81  tff(c_6771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_3879, c_6769])).
% 7.60/2.81  tff(c_6772, plain, (k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitRight, [status(thm)], [c_3833])).
% 7.60/2.81  tff(c_8197, plain, (![A_1025, B_1026, C_1027, D_1028]: (k7_mcart_1(A_1025, B_1026, C_1027, D_1028)=k2_mcart_1(D_1028) | ~m1_subset_1(D_1028, k3_zfmisc_1(A_1025, B_1026, C_1027)) | k1_xboole_0=C_1027 | k1_xboole_0=B_1026 | k1_xboole_0=A_1025)), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.60/2.81  tff(c_8203, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11') | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_94, c_8197])).
% 7.60/2.81  tff(c_8206, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_8203])).
% 7.60/2.81  tff(c_10321, plain, (![A_1176, B_1177, C_1178, D_1179]: (k3_mcart_1(k5_mcart_1(A_1176, B_1177, C_1178, D_1179), k6_mcart_1(A_1176, B_1177, C_1178, D_1179), k7_mcart_1(A_1176, B_1177, C_1178, D_1179))=D_1179 | ~m1_subset_1(D_1179, k3_zfmisc_1(A_1176, B_1177, C_1178)) | k1_xboole_0=C_1178 | k1_xboole_0=B_1177 | k1_xboole_0=A_1176)), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.60/2.81  tff(c_10408, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k2_mcart_1('#skF_11'))='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_8206, c_10321])).
% 7.60/2.81  tff(c_10419, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), '#skF_11', k2_mcart_1('#skF_11'))='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_6772, c_10408])).
% 7.60/2.81  tff(c_10421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_98, c_96, c_7001, c_10419])).
% 7.60/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.81  
% 7.60/2.81  Inference rules
% 7.60/2.81  ----------------------
% 7.60/2.81  #Ref     : 18
% 7.60/2.81  #Sup     : 2360
% 7.60/2.81  #Fact    : 10
% 7.60/2.81  #Define  : 0
% 7.60/2.81  #Split   : 2
% 7.60/2.81  #Chain   : 0
% 7.60/2.81  #Close   : 0
% 7.60/2.81  
% 7.60/2.81  Ordering : KBO
% 7.60/2.81  
% 7.60/2.81  Simplification rules
% 7.60/2.81  ----------------------
% 7.60/2.81  #Subsume      : 440
% 7.60/2.81  #Demod        : 886
% 7.60/2.81  #Tautology    : 688
% 7.60/2.81  #SimpNegUnit  : 375
% 7.60/2.81  #BackRed      : 4
% 7.60/2.81  
% 7.60/2.81  #Partial instantiations: 0
% 7.60/2.81  #Strategies tried      : 1
% 7.60/2.81  
% 7.60/2.81  Timing (in seconds)
% 7.60/2.81  ----------------------
% 7.60/2.81  Preprocessing        : 0.36
% 7.60/2.81  Parsing              : 0.18
% 7.60/2.81  CNF conversion       : 0.03
% 7.60/2.81  Main loop            : 1.67
% 7.60/2.81  Inferencing          : 0.54
% 7.60/2.81  Reduction            : 0.54
% 7.60/2.81  Demodulation         : 0.36
% 7.60/2.81  BG Simplification    : 0.07
% 7.60/2.81  Subsumption          : 0.39
% 7.60/2.81  Abstraction          : 0.11
% 7.60/2.81  MUC search           : 0.00
% 7.60/2.81  Cooper               : 0.00
% 7.60/2.81  Total                : 2.07
% 7.60/2.81  Index Insertion      : 0.00
% 7.60/2.81  Index Deletion       : 0.00
% 7.60/2.81  Index Matching       : 0.00
% 7.60/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
