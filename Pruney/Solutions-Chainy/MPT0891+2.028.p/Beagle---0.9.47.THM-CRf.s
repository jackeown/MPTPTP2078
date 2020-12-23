%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:44 EST 2020

% Result     : Theorem 9.16s
% Output     : CNFRefutation 9.33s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 215 expanded)
%              Number of leaves         :   40 (  94 expanded)
%              Depth                    :    9
%              Number of atoms          :  176 ( 480 expanded)
%              Number of equality atoms :  144 ( 384 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_122,axiom,(
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

tff(f_102,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_105,plain,(
    ! [A_67] : k2_tarski(A_67,A_67) = k1_tarski(A_67) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [D_10,B_6] : r2_hidden(D_10,k2_tarski(D_10,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,(
    ! [A_67] : r2_hidden(A_67,k1_tarski(A_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_12])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_156])).

tff(c_6142,plain,(
    ! [A_13395] : k4_xboole_0(A_13395,A_13395) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_174])).

tff(c_30,plain,(
    ! [B_15,A_14] :
      ( ~ r2_hidden(B_15,A_14)
      | k4_xboole_0(A_14,k1_tarski(B_15)) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6155,plain,(
    ! [B_15] :
      ( ~ r2_hidden(B_15,k1_tarski(B_15))
      | k1_tarski(B_15) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6142,c_30])).

tff(c_6174,plain,(
    ! [B_15] : k1_tarski(B_15) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_6155])).

tff(c_48,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_3'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6252,plain,(
    ! [D_13413,B_13414,A_13415] :
      ( D_13413 = B_13414
      | D_13413 = A_13415
      | ~ r2_hidden(D_13413,k2_tarski(A_13415,B_13414)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6280,plain,(
    ! [D_13419,A_13420] :
      ( D_13419 = A_13420
      | D_13419 = A_13420
      | ~ r2_hidden(D_13419,k1_tarski(A_13420)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_6252])).

tff(c_6284,plain,(
    ! [A_13420] :
      ( '#skF_3'(k1_tarski(A_13420)) = A_13420
      | k1_tarski(A_13420) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_6280])).

tff(c_6290,plain,(
    ! [A_13420] : '#skF_3'(k1_tarski(A_13420)) = A_13420 ),
    inference(negUnitSimplification,[status(thm)],[c_6174,c_6284])).

tff(c_14763,plain,(
    ! [D_28301,A_28302,C_28303,E_28304] :
      ( ~ r2_hidden(D_28301,A_28302)
      | k3_mcart_1(C_28303,D_28301,E_28304) != '#skF_3'(A_28302)
      | k1_xboole_0 = A_28302 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14769,plain,(
    ! [C_28303,A_67,E_28304] :
      ( k3_mcart_1(C_28303,A_67,E_28304) != '#skF_3'(k1_tarski(A_67))
      | k1_tarski(A_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_111,c_14763])).

tff(c_14775,plain,(
    ! [C_28303,A_67,E_28304] :
      ( k3_mcart_1(C_28303,A_67,E_28304) != A_67
      | k1_tarski(A_67) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6290,c_14769])).

tff(c_14776,plain,(
    ! [C_28303,A_67,E_28304] : k3_mcart_1(C_28303,A_67,E_28304) != A_67 ),
    inference(negUnitSimplification,[status(thm)],[c_6174,c_14775])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_6214,plain,(
    ! [A_13401,B_13402,C_13403] : k4_tarski(k4_tarski(A_13401,B_13402),C_13403) = k3_mcart_1(A_13401,B_13402,C_13403) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_64,plain,(
    ! [A_54,B_55] : k2_mcart_1(k4_tarski(A_54,B_55)) = B_55 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    ! [B_28,C_29] : k2_mcart_1(k4_tarski(B_28,C_29)) != k4_tarski(B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    ! [B_28,C_29] : k4_tarski(B_28,C_29) != C_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_44])).

tff(c_6232,plain,(
    ! [A_13401,B_13402,C_13403] : k3_mcart_1(A_13401,B_13402,C_13403) != C_13403 ),
    inference(superposition,[status(thm),theory(equality)],[c_6214,c_76])).

tff(c_179,plain,(
    ! [A_82] : k4_xboole_0(A_82,A_82) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_174])).

tff(c_192,plain,(
    ! [B_15] :
      ( ~ r2_hidden(B_15,k1_tarski(B_15))
      | k1_tarski(B_15) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_30])).

tff(c_211,plain,(
    ! [B_15] : k1_tarski(B_15) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_192])).

tff(c_293,plain,(
    ! [D_100,B_101,A_102] :
      ( D_100 = B_101
      | D_100 = A_102
      | ~ r2_hidden(D_100,k2_tarski(A_102,B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_321,plain,(
    ! [D_106,A_107] :
      ( D_106 = A_107
      | D_106 = A_107
      | ~ r2_hidden(D_106,k1_tarski(A_107)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_293])).

tff(c_325,plain,(
    ! [A_107] :
      ( '#skF_3'(k1_tarski(A_107)) = A_107
      | k1_tarski(A_107) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_321])).

tff(c_331,plain,(
    ! [A_107] : '#skF_3'(k1_tarski(A_107)) = A_107 ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_325])).

tff(c_394,plain,(
    ! [C_113,A_114,D_115,E_116] :
      ( ~ r2_hidden(C_113,A_114)
      | k3_mcart_1(C_113,D_115,E_116) != '#skF_3'(A_114)
      | k1_xboole_0 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_400,plain,(
    ! [A_67,D_115,E_116] :
      ( k3_mcart_1(A_67,D_115,E_116) != '#skF_3'(k1_tarski(A_67))
      | k1_tarski(A_67) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_111,c_394])).

tff(c_406,plain,(
    ! [A_67,D_115,E_116] :
      ( k3_mcart_1(A_67,D_115,E_116) != A_67
      | k1_tarski(A_67) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_400])).

tff(c_407,plain,(
    ! [A_67,D_115,E_116] : k3_mcart_1(A_67,D_115,E_116) != A_67 ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_406])).

tff(c_66,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_178,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_4503,plain,(
    ! [A_10141,B_10142,C_10143,D_10144] :
      ( k7_mcart_1(A_10141,B_10142,C_10143,D_10144) = k2_mcart_1(D_10144)
      | ~ m1_subset_1(D_10144,k3_zfmisc_1(A_10141,B_10142,C_10143))
      | k1_xboole_0 = C_10143
      | k1_xboole_0 = B_10142
      | k1_xboole_0 = A_10141 ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4512,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_68,c_4503])).

tff(c_4515,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_70,c_4512])).

tff(c_6045,plain,(
    ! [A_13268,B_13269,C_13270,D_13271] :
      ( k3_mcart_1(k5_mcart_1(A_13268,B_13269,C_13270,D_13271),k6_mcart_1(A_13268,B_13269,C_13270,D_13271),k7_mcart_1(A_13268,B_13269,C_13270,D_13271)) = D_13271
      | ~ m1_subset_1(D_13271,k3_zfmisc_1(A_13268,B_13269,C_13270))
      | k1_xboole_0 = C_13270
      | k1_xboole_0 = B_13269
      | k1_xboole_0 = A_13268 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6114,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4515,c_6045])).

tff(c_6137,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_178,c_6114])).

tff(c_6139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_70,c_407,c_6137])).

tff(c_6140,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_6307,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_6140])).

tff(c_14571,plain,(
    ! [A_28161,B_28162,C_28163,D_28164] :
      ( k3_mcart_1(k5_mcart_1(A_28161,B_28162,C_28163,D_28164),k6_mcart_1(A_28161,B_28162,C_28163,D_28164),k7_mcart_1(A_28161,B_28162,C_28163,D_28164)) = D_28164
      | ~ m1_subset_1(D_28164,k3_zfmisc_1(A_28161,B_28162,C_28163))
      | k1_xboole_0 = C_28163
      | k1_xboole_0 = B_28162
      | k1_xboole_0 = A_28161 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14660,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6307,c_14571])).

tff(c_14668,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_14660])).

tff(c_14670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_70,c_6232,c_14668])).

tff(c_14671,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6140])).

tff(c_18768,plain,(
    ! [A_38386,B_38387,C_38388,D_38389] :
      ( k7_mcart_1(A_38386,B_38387,C_38388,D_38389) = k2_mcart_1(D_38389)
      | ~ m1_subset_1(D_38389,k3_zfmisc_1(A_38386,B_38387,C_38388))
      | k1_xboole_0 = C_38388
      | k1_xboole_0 = B_38387
      | k1_xboole_0 = A_38386 ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_18777,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_68,c_18768])).

tff(c_18780,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_70,c_18777])).

tff(c_19792,plain,(
    ! [A_41003,B_41004,C_41005,D_41006] :
      ( k3_mcart_1(k5_mcart_1(A_41003,B_41004,C_41005,D_41006),k6_mcart_1(A_41003,B_41004,C_41005,D_41006),k7_mcart_1(A_41003,B_41004,C_41005,D_41006)) = D_41006
      | ~ m1_subset_1(D_41006,k3_zfmisc_1(A_41003,B_41004,C_41005))
      | k1_xboole_0 = C_41005
      | k1_xboole_0 = B_41004
      | k1_xboole_0 = A_41003 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_19851,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_18780,c_19792])).

tff(c_19870,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_14671,c_19851])).

tff(c_19872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_70,c_14776,c_19870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:00:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.16/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.16/3.18  
% 9.16/3.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.33/3.18  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 9.33/3.18  
% 9.33/3.18  %Foreground sorts:
% 9.33/3.18  
% 9.33/3.18  
% 9.33/3.18  %Background operators:
% 9.33/3.18  
% 9.33/3.18  
% 9.33/3.18  %Foreground operators:
% 9.33/3.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.33/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.33/3.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.33/3.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.33/3.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.33/3.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.33/3.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.33/3.18  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 9.33/3.18  tff('#skF_7', type, '#skF_7': $i).
% 9.33/3.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.33/3.18  tff('#skF_5', type, '#skF_5': $i).
% 9.33/3.18  tff('#skF_6', type, '#skF_6': $i).
% 9.33/3.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.33/3.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.33/3.18  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 9.33/3.18  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 9.33/3.18  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 9.33/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.33/3.18  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 9.33/3.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.33/3.18  tff('#skF_4', type, '#skF_4': $i).
% 9.33/3.18  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.33/3.18  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 9.33/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.33/3.18  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 9.33/3.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.33/3.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.33/3.18  
% 9.33/3.20  tff(f_150, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 9.33/3.20  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.33/3.20  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 9.33/3.20  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.33/3.20  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.33/3.20  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.33/3.20  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 9.33/3.20  tff(f_86, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 9.33/3.20  tff(f_59, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 9.33/3.20  tff(f_126, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 9.33/3.20  tff(f_70, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 9.33/3.20  tff(f_122, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 9.33/3.20  tff(f_102, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 9.33/3.20  tff(c_74, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.33/3.20  tff(c_72, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.33/3.20  tff(c_70, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.33/3.20  tff(c_105, plain, (![A_67]: (k2_tarski(A_67, A_67)=k1_tarski(A_67))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.33/3.20  tff(c_12, plain, (![D_10, B_6]: (r2_hidden(D_10, k2_tarski(D_10, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.33/3.20  tff(c_111, plain, (![A_67]: (r2_hidden(A_67, k1_tarski(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_12])).
% 9.33/3.20  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.33/3.20  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.33/3.20  tff(c_156, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.33/3.20  tff(c_174, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_156])).
% 9.33/3.20  tff(c_6142, plain, (![A_13395]: (k4_xboole_0(A_13395, A_13395)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_174])).
% 9.33/3.20  tff(c_30, plain, (![B_15, A_14]: (~r2_hidden(B_15, A_14) | k4_xboole_0(A_14, k1_tarski(B_15))!=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.33/3.20  tff(c_6155, plain, (![B_15]: (~r2_hidden(B_15, k1_tarski(B_15)) | k1_tarski(B_15)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6142, c_30])).
% 9.33/3.20  tff(c_6174, plain, (![B_15]: (k1_tarski(B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_6155])).
% 9.33/3.20  tff(c_48, plain, (![A_30]: (r2_hidden('#skF_3'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.33/3.20  tff(c_26, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.33/3.20  tff(c_6252, plain, (![D_13413, B_13414, A_13415]: (D_13413=B_13414 | D_13413=A_13415 | ~r2_hidden(D_13413, k2_tarski(A_13415, B_13414)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.33/3.20  tff(c_6280, plain, (![D_13419, A_13420]: (D_13419=A_13420 | D_13419=A_13420 | ~r2_hidden(D_13419, k1_tarski(A_13420)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_6252])).
% 9.33/3.20  tff(c_6284, plain, (![A_13420]: ('#skF_3'(k1_tarski(A_13420))=A_13420 | k1_tarski(A_13420)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_6280])).
% 9.33/3.20  tff(c_6290, plain, (![A_13420]: ('#skF_3'(k1_tarski(A_13420))=A_13420)), inference(negUnitSimplification, [status(thm)], [c_6174, c_6284])).
% 9.33/3.20  tff(c_14763, plain, (![D_28301, A_28302, C_28303, E_28304]: (~r2_hidden(D_28301, A_28302) | k3_mcart_1(C_28303, D_28301, E_28304)!='#skF_3'(A_28302) | k1_xboole_0=A_28302)), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.33/3.20  tff(c_14769, plain, (![C_28303, A_67, E_28304]: (k3_mcart_1(C_28303, A_67, E_28304)!='#skF_3'(k1_tarski(A_67)) | k1_tarski(A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_111, c_14763])).
% 9.33/3.20  tff(c_14775, plain, (![C_28303, A_67, E_28304]: (k3_mcart_1(C_28303, A_67, E_28304)!=A_67 | k1_tarski(A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6290, c_14769])).
% 9.33/3.20  tff(c_14776, plain, (![C_28303, A_67, E_28304]: (k3_mcart_1(C_28303, A_67, E_28304)!=A_67)), inference(negUnitSimplification, [status(thm)], [c_6174, c_14775])).
% 9.33/3.20  tff(c_68, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.33/3.20  tff(c_6214, plain, (![A_13401, B_13402, C_13403]: (k4_tarski(k4_tarski(A_13401, B_13402), C_13403)=k3_mcart_1(A_13401, B_13402, C_13403))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.33/3.20  tff(c_64, plain, (![A_54, B_55]: (k2_mcart_1(k4_tarski(A_54, B_55))=B_55)), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.33/3.20  tff(c_44, plain, (![B_28, C_29]: (k2_mcart_1(k4_tarski(B_28, C_29))!=k4_tarski(B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.33/3.20  tff(c_76, plain, (![B_28, C_29]: (k4_tarski(B_28, C_29)!=C_29)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_44])).
% 9.33/3.20  tff(c_6232, plain, (![A_13401, B_13402, C_13403]: (k3_mcart_1(A_13401, B_13402, C_13403)!=C_13403)), inference(superposition, [status(thm), theory('equality')], [c_6214, c_76])).
% 9.33/3.20  tff(c_179, plain, (![A_82]: (k4_xboole_0(A_82, A_82)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_174])).
% 9.33/3.20  tff(c_192, plain, (![B_15]: (~r2_hidden(B_15, k1_tarski(B_15)) | k1_tarski(B_15)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_179, c_30])).
% 9.33/3.20  tff(c_211, plain, (![B_15]: (k1_tarski(B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_192])).
% 9.33/3.20  tff(c_293, plain, (![D_100, B_101, A_102]: (D_100=B_101 | D_100=A_102 | ~r2_hidden(D_100, k2_tarski(A_102, B_101)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.33/3.20  tff(c_321, plain, (![D_106, A_107]: (D_106=A_107 | D_106=A_107 | ~r2_hidden(D_106, k1_tarski(A_107)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_293])).
% 9.33/3.20  tff(c_325, plain, (![A_107]: ('#skF_3'(k1_tarski(A_107))=A_107 | k1_tarski(A_107)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_321])).
% 9.33/3.20  tff(c_331, plain, (![A_107]: ('#skF_3'(k1_tarski(A_107))=A_107)), inference(negUnitSimplification, [status(thm)], [c_211, c_325])).
% 9.33/3.20  tff(c_394, plain, (![C_113, A_114, D_115, E_116]: (~r2_hidden(C_113, A_114) | k3_mcart_1(C_113, D_115, E_116)!='#skF_3'(A_114) | k1_xboole_0=A_114)), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.33/3.20  tff(c_400, plain, (![A_67, D_115, E_116]: (k3_mcart_1(A_67, D_115, E_116)!='#skF_3'(k1_tarski(A_67)) | k1_tarski(A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_111, c_394])).
% 9.33/3.20  tff(c_406, plain, (![A_67, D_115, E_116]: (k3_mcart_1(A_67, D_115, E_116)!=A_67 | k1_tarski(A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_331, c_400])).
% 9.33/3.20  tff(c_407, plain, (![A_67, D_115, E_116]: (k3_mcart_1(A_67, D_115, E_116)!=A_67)), inference(negUnitSimplification, [status(thm)], [c_211, c_406])).
% 9.33/3.20  tff(c_66, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.33/3.20  tff(c_178, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_66])).
% 9.33/3.20  tff(c_4503, plain, (![A_10141, B_10142, C_10143, D_10144]: (k7_mcart_1(A_10141, B_10142, C_10143, D_10144)=k2_mcart_1(D_10144) | ~m1_subset_1(D_10144, k3_zfmisc_1(A_10141, B_10142, C_10143)) | k1_xboole_0=C_10143 | k1_xboole_0=B_10142 | k1_xboole_0=A_10141)), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.33/3.20  tff(c_4512, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_68, c_4503])).
% 9.33/3.20  tff(c_4515, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_70, c_4512])).
% 9.33/3.20  tff(c_6045, plain, (![A_13268, B_13269, C_13270, D_13271]: (k3_mcart_1(k5_mcart_1(A_13268, B_13269, C_13270, D_13271), k6_mcart_1(A_13268, B_13269, C_13270, D_13271), k7_mcart_1(A_13268, B_13269, C_13270, D_13271))=D_13271 | ~m1_subset_1(D_13271, k3_zfmisc_1(A_13268, B_13269, C_13270)) | k1_xboole_0=C_13270 | k1_xboole_0=B_13269 | k1_xboole_0=A_13268)), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.33/3.20  tff(c_6114, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4515, c_6045])).
% 9.33/3.20  tff(c_6137, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_178, c_6114])).
% 9.33/3.20  tff(c_6139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_70, c_407, c_6137])).
% 9.33/3.20  tff(c_6140, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_66])).
% 9.33/3.20  tff(c_6307, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_6140])).
% 9.33/3.20  tff(c_14571, plain, (![A_28161, B_28162, C_28163, D_28164]: (k3_mcart_1(k5_mcart_1(A_28161, B_28162, C_28163, D_28164), k6_mcart_1(A_28161, B_28162, C_28163, D_28164), k7_mcart_1(A_28161, B_28162, C_28163, D_28164))=D_28164 | ~m1_subset_1(D_28164, k3_zfmisc_1(A_28161, B_28162, C_28163)) | k1_xboole_0=C_28163 | k1_xboole_0=B_28162 | k1_xboole_0=A_28161)), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.33/3.20  tff(c_14660, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6307, c_14571])).
% 9.33/3.20  tff(c_14668, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_14660])).
% 9.33/3.20  tff(c_14670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_70, c_6232, c_14668])).
% 9.33/3.20  tff(c_14671, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_6140])).
% 9.33/3.20  tff(c_18768, plain, (![A_38386, B_38387, C_38388, D_38389]: (k7_mcart_1(A_38386, B_38387, C_38388, D_38389)=k2_mcart_1(D_38389) | ~m1_subset_1(D_38389, k3_zfmisc_1(A_38386, B_38387, C_38388)) | k1_xboole_0=C_38388 | k1_xboole_0=B_38387 | k1_xboole_0=A_38386)), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.33/3.20  tff(c_18777, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_68, c_18768])).
% 9.33/3.20  tff(c_18780, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_70, c_18777])).
% 9.33/3.20  tff(c_19792, plain, (![A_41003, B_41004, C_41005, D_41006]: (k3_mcart_1(k5_mcart_1(A_41003, B_41004, C_41005, D_41006), k6_mcart_1(A_41003, B_41004, C_41005, D_41006), k7_mcart_1(A_41003, B_41004, C_41005, D_41006))=D_41006 | ~m1_subset_1(D_41006, k3_zfmisc_1(A_41003, B_41004, C_41005)) | k1_xboole_0=C_41005 | k1_xboole_0=B_41004 | k1_xboole_0=A_41003)), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.33/3.20  tff(c_19851, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_18780, c_19792])).
% 9.33/3.20  tff(c_19870, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_14671, c_19851])).
% 9.33/3.20  tff(c_19872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_70, c_14776, c_19870])).
% 9.33/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.33/3.20  
% 9.33/3.20  Inference rules
% 9.33/3.20  ----------------------
% 9.33/3.20  #Ref     : 10
% 9.33/3.20  #Sup     : 2366
% 9.33/3.20  #Fact    : 24
% 9.33/3.20  #Define  : 0
% 9.33/3.20  #Split   : 2
% 9.33/3.20  #Chain   : 0
% 9.33/3.20  #Close   : 0
% 9.33/3.20  
% 9.33/3.20  Ordering : KBO
% 9.33/3.20  
% 9.33/3.20  Simplification rules
% 9.33/3.20  ----------------------
% 9.33/3.20  #Subsume      : 393
% 9.33/3.20  #Demod        : 788
% 9.33/3.20  #Tautology    : 783
% 9.33/3.20  #SimpNegUnit  : 276
% 9.33/3.20  #BackRed      : 1
% 9.33/3.20  
% 9.33/3.20  #Partial instantiations: 21648
% 9.33/3.20  #Strategies tried      : 1
% 9.33/3.20  
% 9.33/3.20  Timing (in seconds)
% 9.33/3.20  ----------------------
% 9.33/3.20  Preprocessing        : 0.44
% 9.33/3.20  Parsing              : 0.23
% 9.33/3.20  CNF conversion       : 0.03
% 9.33/3.20  Main loop            : 1.99
% 9.33/3.20  Inferencing          : 1.04
% 9.33/3.20  Reduction            : 0.48
% 9.33/3.20  Demodulation         : 0.32
% 9.33/3.20  BG Simplification    : 0.10
% 9.33/3.20  Subsumption          : 0.26
% 9.33/3.20  Abstraction          : 0.09
% 9.33/3.20  MUC search           : 0.00
% 9.33/3.20  Cooper               : 0.00
% 9.33/3.20  Total                : 2.47
% 9.33/3.20  Index Insertion      : 0.00
% 9.33/3.20  Index Deletion       : 0.00
% 9.33/3.20  Index Matching       : 0.00
% 9.33/3.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
