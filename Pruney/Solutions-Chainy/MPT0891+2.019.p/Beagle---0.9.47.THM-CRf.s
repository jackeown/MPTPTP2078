%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:42 EST 2020

% Result     : Theorem 11.50s
% Output     : CNFRefutation 11.70s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 490 expanded)
%              Number of leaves         :   39 ( 182 expanded)
%              Depth                    :   15
%              Number of atoms          :  232 (1136 expanded)
%              Number of equality atoms :  137 ( 687 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_9 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_2 > #skF_7 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_127,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_83,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    ! [A_43] : k2_zfmisc_1(A_43,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34907,plain,(
    ! [E_54596,F_54597,A_54598,B_54599] :
      ( r2_hidden(k4_tarski(E_54596,F_54597),k2_zfmisc_1(A_54598,B_54599))
      | ~ r2_hidden(F_54597,B_54599)
      | ~ r2_hidden(E_54596,A_54598) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34927,plain,(
    ! [E_54603,F_54604,A_54605] :
      ( r2_hidden(k4_tarski(E_54603,F_54604),k1_xboole_0)
      | ~ r2_hidden(F_54604,k1_xboole_0)
      | ~ r2_hidden(E_54603,A_54605) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_34907])).

tff(c_34939,plain,(
    ! [D_6,F_54604] :
      ( r2_hidden(k4_tarski(D_6,F_54604),k1_xboole_0)
      | ~ r2_hidden(F_54604,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_34927])).

tff(c_68,plain,(
    ! [A_75,B_76] : k1_mcart_1(k4_tarski(A_75,B_76)) = A_75 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_39475,plain,(
    ! [A_67839,B_67840,D_67841] :
      ( k4_tarski('#skF_7'(A_67839,B_67840,k2_zfmisc_1(A_67839,B_67840),D_67841),'#skF_8'(A_67839,B_67840,k2_zfmisc_1(A_67839,B_67840),D_67841)) = D_67841
      | ~ r2_hidden(D_67841,k2_zfmisc_1(A_67839,B_67840)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_39604,plain,(
    ! [A_69203,B_69204,D_69205] :
      ( '#skF_7'(A_69203,B_69204,k2_zfmisc_1(A_69203,B_69204),D_69205) = k1_mcart_1(D_69205)
      | ~ r2_hidden(D_69205,k2_zfmisc_1(A_69203,B_69204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39475,c_68])).

tff(c_39646,plain,(
    ! [A_43,D_69205] :
      ( '#skF_7'(A_43,k1_xboole_0,k2_zfmisc_1(A_43,k1_xboole_0),D_69205) = k1_mcart_1(D_69205)
      | ~ r2_hidden(D_69205,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_39604])).

tff(c_39667,plain,(
    ! [D_69374,A_69375] :
      ( k1_mcart_1(D_69374) = '#skF_7'(A_69375,k1_xboole_0,k1_xboole_0,D_69374)
      | ~ r2_hidden(D_69374,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_39646])).

tff(c_39707,plain,(
    ! [D_6,F_54604,A_69375] :
      ( k1_mcart_1(k4_tarski(D_6,F_54604)) = '#skF_7'(A_69375,k1_xboole_0,k1_xboole_0,k4_tarski(D_6,F_54604))
      | ~ r2_hidden(F_54604,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34939,c_39667])).

tff(c_39848,plain,(
    ! [A_70058,D_70059,F_70060] :
      ( '#skF_7'(A_70058,k1_xboole_0,k1_xboole_0,k4_tarski(D_70059,F_70060)) = D_70059
      | ~ r2_hidden(F_70060,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_39707])).

tff(c_34953,plain,(
    ! [A_54608,B_54609,D_54610] :
      ( r2_hidden('#skF_7'(A_54608,B_54609,k2_zfmisc_1(A_54608,B_54609),D_54610),A_54608)
      | ~ r2_hidden(D_54610,k2_zfmisc_1(A_54608,B_54609)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34967,plain,(
    ! [A_43,D_54610] :
      ( r2_hidden('#skF_7'(A_43,k1_xboole_0,k1_xboole_0,D_54610),A_43)
      | ~ r2_hidden(D_54610,k2_zfmisc_1(A_43,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_34953])).

tff(c_34975,plain,(
    ! [A_43,D_54610] :
      ( r2_hidden('#skF_7'(A_43,k1_xboole_0,k1_xboole_0,D_54610),A_43)
      | ~ r2_hidden(D_54610,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_34967])).

tff(c_40021,plain,(
    ! [D_70742,A_70743,F_70744] :
      ( r2_hidden(D_70742,A_70743)
      | ~ r2_hidden(k4_tarski(D_70742,F_70744),k1_xboole_0)
      | ~ r2_hidden(F_70744,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39848,c_34975])).

tff(c_40035,plain,(
    ! [D_6,A_70743,F_54604] :
      ( r2_hidden(D_6,A_70743)
      | ~ r2_hidden(F_54604,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34939,c_40021])).

tff(c_40036,plain,(
    ! [F_54604] : ~ r2_hidden(F_54604,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_40035])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_74,plain,(
    m1_subset_1('#skF_13',k3_zfmisc_1('#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_164,plain,(
    ! [A_100,B_101,C_102] : k4_tarski(k4_tarski(A_100,B_101),C_102) = k3_mcart_1(A_100,B_101,C_102) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,(
    ! [A_75,B_76] : k2_mcart_1(k4_tarski(A_75,B_76)) = B_76 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    ! [B_54,C_55] : k2_mcart_1(k4_tarski(B_54,C_55)) != k4_tarski(B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_82,plain,(
    ! [B_54,C_55] : k4_tarski(B_54,C_55) != C_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_56])).

tff(c_179,plain,(
    ! [A_100,B_101,C_102] : k3_mcart_1(A_100,B_101,C_102) != C_102 ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_82])).

tff(c_173,plain,(
    ! [A_100,B_101,C_102] : k2_mcart_1(k3_mcart_1(A_100,B_101,C_102)) = C_102 ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_70])).

tff(c_50,plain,(
    ! [B_44] : k2_zfmisc_1(k1_xboole_0,B_44) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_372,plain,(
    ! [E_149,F_150,A_151,B_152] :
      ( r2_hidden(k4_tarski(E_149,F_150),k2_zfmisc_1(A_151,B_152))
      | ~ r2_hidden(F_150,B_152)
      | ~ r2_hidden(E_149,A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_476,plain,(
    ! [E_168,F_169,B_170] :
      ( r2_hidden(k4_tarski(E_168,F_169),k1_xboole_0)
      | ~ r2_hidden(F_169,B_170)
      | ~ r2_hidden(E_168,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_372])).

tff(c_502,plain,(
    ! [E_168,D_6] :
      ( r2_hidden(k4_tarski(E_168,D_6),k1_xboole_0)
      | ~ r2_hidden(E_168,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_476])).

tff(c_5040,plain,(
    ! [A_13455,B_13456,D_13457] :
      ( k4_tarski('#skF_7'(A_13455,B_13456,k2_zfmisc_1(A_13455,B_13456),D_13457),'#skF_8'(A_13455,B_13456,k2_zfmisc_1(A_13455,B_13456),D_13457)) = D_13457
      | ~ r2_hidden(D_13457,k2_zfmisc_1(A_13455,B_13456)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5169,plain,(
    ! [A_14819,B_14820,D_14821] :
      ( '#skF_8'(A_14819,B_14820,k2_zfmisc_1(A_14819,B_14820),D_14821) = k2_mcart_1(D_14821)
      | ~ r2_hidden(D_14821,k2_zfmisc_1(A_14819,B_14820)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5040,c_70])).

tff(c_5213,plain,(
    ! [B_44,D_14821] :
      ( '#skF_8'(k1_xboole_0,B_44,k2_zfmisc_1(k1_xboole_0,B_44),D_14821) = k2_mcart_1(D_14821)
      | ~ r2_hidden(D_14821,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_5169])).

tff(c_5310,plain,(
    ! [D_15333,B_15334] :
      ( k2_mcart_1(D_15333) = '#skF_8'(k1_xboole_0,B_15334,k1_xboole_0,D_15333)
      | ~ r2_hidden(D_15333,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5213])).

tff(c_5338,plain,(
    ! [E_168,D_6,B_15334] :
      ( k2_mcart_1(k4_tarski(E_168,D_6)) = '#skF_8'(k1_xboole_0,B_15334,k1_xboole_0,k4_tarski(E_168,D_6))
      | ~ r2_hidden(E_168,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_502,c_5310])).

tff(c_5418,plain,(
    ! [B_15674,E_15675,D_15676] :
      ( '#skF_8'(k1_xboole_0,B_15674,k1_xboole_0,k4_tarski(E_15675,D_15676)) = D_15676
      | ~ r2_hidden(E_15675,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5338])).

tff(c_517,plain,(
    ! [A_173,B_174,D_175] :
      ( r2_hidden('#skF_8'(A_173,B_174,k2_zfmisc_1(A_173,B_174),D_175),B_174)
      | ~ r2_hidden(D_175,k2_zfmisc_1(A_173,B_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_531,plain,(
    ! [A_43,D_175] :
      ( r2_hidden('#skF_8'(A_43,k1_xboole_0,k1_xboole_0,D_175),k1_xboole_0)
      | ~ r2_hidden(D_175,k2_zfmisc_1(A_43,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_517])).

tff(c_539,plain,(
    ! [A_43,D_175] :
      ( r2_hidden('#skF_8'(A_43,k1_xboole_0,k1_xboole_0,D_175),k1_xboole_0)
      | ~ r2_hidden(D_175,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_531])).

tff(c_5601,plain,(
    ! [D_16358,E_16359] :
      ( r2_hidden(D_16358,k1_xboole_0)
      | ~ r2_hidden(k4_tarski(E_16359,D_16358),k1_xboole_0)
      | ~ r2_hidden(E_16359,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5418,c_539])).

tff(c_5618,plain,(
    ! [D_6,E_168] :
      ( r2_hidden(D_6,k1_xboole_0)
      | ~ r2_hidden(E_168,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_502,c_5601])).

tff(c_5620,plain,(
    ! [E_168] : ~ r2_hidden(E_168,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5618])).

tff(c_72,plain,
    ( k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_13'
    | k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_13'
    | k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_201,plain,(
    k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_6336,plain,(
    ! [A_18745,B_18746,C_18747,D_18748] :
      ( k3_mcart_1(k5_mcart_1(A_18745,B_18746,C_18747,D_18748),k6_mcart_1(A_18745,B_18746,C_18747,D_18748),k7_mcart_1(A_18745,B_18746,C_18747,D_18748)) = D_18748
      | ~ m1_subset_1(D_18748,k3_zfmisc_1(A_18745,B_18746,C_18747))
      | k1_xboole_0 = C_18747
      | k1_xboole_0 = B_18746
      | k1_xboole_0 = A_18745 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6405,plain,
    ( k3_mcart_1('#skF_13',k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13'),k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13')) = '#skF_13'
    | ~ m1_subset_1('#skF_13',k3_zfmisc_1('#skF_10','#skF_11','#skF_12'))
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_6336])).

tff(c_6409,plain,
    ( k3_mcart_1('#skF_13',k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13'),k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13')) = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6405])).

tff(c_6410,plain,(
    k3_mcart_1('#skF_13',k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13'),k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13')) = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_76,c_6409])).

tff(c_60,plain,(
    ! [A_56] :
      ( r2_hidden('#skF_9'(A_56),A_56)
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_148,plain,(
    ! [D_97,B_98,A_99] :
      ( D_97 = B_98
      | D_97 = A_99
      | ~ r2_hidden(D_97,k2_tarski(A_99,B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_159,plain,(
    ! [A_99,B_98] :
      ( '#skF_9'(k2_tarski(A_99,B_98)) = B_98
      | '#skF_9'(k2_tarski(A_99,B_98)) = A_99
      | k2_tarski(A_99,B_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60,c_148])).

tff(c_746,plain,(
    ! [B_214] :
      ( k2_tarski(B_214,B_214) = k1_xboole_0
      | '#skF_9'(k2_tarski(B_214,B_214)) = B_214 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_159])).

tff(c_257,plain,(
    ! [C_120,A_121,D_122,E_123] :
      ( ~ r2_hidden(C_120,A_121)
      | k3_mcart_1(C_120,D_122,E_123) != '#skF_9'(A_121)
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_265,plain,(
    ! [D_6,D_122,E_123,B_2] :
      ( k3_mcart_1(D_6,D_122,E_123) != '#skF_9'(k2_tarski(D_6,B_2))
      | k2_tarski(D_6,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_257])).

tff(c_761,plain,(
    ! [B_214,D_122,E_123] :
      ( k3_mcart_1(B_214,D_122,E_123) != B_214
      | k2_tarski(B_214,B_214) = k1_xboole_0
      | k2_tarski(B_214,B_214) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_265])).

tff(c_6471,plain,(
    k2_tarski('#skF_13','#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6410,c_761])).

tff(c_6509,plain,(
    r2_hidden('#skF_13',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6471,c_6])).

tff(c_6697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5620,c_6509])).

tff(c_6698,plain,(
    ! [D_6] : r2_hidden(D_6,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5618])).

tff(c_5231,plain,(
    ! [D_14821,B_44] :
      ( k2_mcart_1(D_14821) = '#skF_8'(k1_xboole_0,B_44,k1_xboole_0,D_14821)
      | ~ r2_hidden(D_14821,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5213])).

tff(c_6843,plain,(
    ! [D_20786,B_20787] : k2_mcart_1(D_20786) = '#skF_8'(k1_xboole_0,B_20787,k1_xboole_0,D_20786) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6698,c_5231])).

tff(c_534,plain,(
    ! [B_44,D_175] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_44,k1_xboole_0,D_175),B_44)
      | ~ r2_hidden(D_175,k2_zfmisc_1(k1_xboole_0,B_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_517])).

tff(c_540,plain,(
    ! [B_44,D_175] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_44,k1_xboole_0,D_175),B_44)
      | ~ r2_hidden(D_175,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_534])).

tff(c_6733,plain,(
    ! [B_44,D_175] : r2_hidden('#skF_8'(k1_xboole_0,B_44,k1_xboole_0,D_175),B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6698,c_540])).

tff(c_6901,plain,(
    ! [D_21296,B_21297] : r2_hidden(k2_mcart_1(D_21296),B_21297) ),
    inference(superposition,[status(thm),theory(equality)],[c_6843,c_6733])).

tff(c_6919,plain,(
    ! [C_102,B_21297] : r2_hidden(C_102,B_21297) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_6901])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6968,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6919,c_2])).

tff(c_28245,plain,(
    ! [D_32671,B_32672] : D_32671 = B_32672 ),
    inference(factorization,[status(thm),theory(equality)],[c_6968])).

tff(c_5115,plain,(
    ! [A_13626,B_13627,D_13628] :
      ( '#skF_8'(A_13626,B_13627,k2_zfmisc_1(A_13626,B_13627),D_13628) != D_13628
      | ~ r2_hidden(D_13628,k2_zfmisc_1(A_13626,B_13627)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5040,c_82])).

tff(c_5127,plain,(
    ! [B_44,D_13628] :
      ( '#skF_8'(k1_xboole_0,B_44,k1_xboole_0,D_13628) != D_13628
      | ~ r2_hidden(D_13628,k2_zfmisc_1(k1_xboole_0,B_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_5115])).

tff(c_5130,plain,(
    ! [B_44,D_13628] :
      ( '#skF_8'(k1_xboole_0,B_44,k1_xboole_0,D_13628) != D_13628
      | ~ r2_hidden(D_13628,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5127])).

tff(c_6718,plain,(
    ! [B_44,D_13628] : '#skF_8'(k1_xboole_0,B_44,k1_xboole_0,D_13628) != D_13628 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6698,c_5130])).

tff(c_6855,plain,(
    ! [D_20786] : k2_mcart_1(D_20786) != D_20786 ),
    inference(superposition,[status(thm),theory(equality)],[c_6843,c_6718])).

tff(c_28745,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_28245,c_6855])).

tff(c_28746,plain,
    ( k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_13'
    | k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_28792,plain,(
    k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_28746])).

tff(c_34751,plain,(
    ! [A_54407,B_54408,C_54409,D_54410] :
      ( k3_mcart_1(k5_mcart_1(A_54407,B_54408,C_54409,D_54410),k6_mcart_1(A_54407,B_54408,C_54409,D_54410),k7_mcart_1(A_54407,B_54408,C_54409,D_54410)) = D_54410
      | ~ m1_subset_1(D_54410,k3_zfmisc_1(A_54407,B_54408,C_54409))
      | k1_xboole_0 = C_54409
      | k1_xboole_0 = B_54408
      | k1_xboole_0 = A_54407 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34827,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13'),k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13'),'#skF_13') = '#skF_13'
    | ~ m1_subset_1('#skF_13',k3_zfmisc_1('#skF_10','#skF_11','#skF_12'))
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_28792,c_34751])).

tff(c_34831,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13'),k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13'),'#skF_13') = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_34827])).

tff(c_34833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_76,c_179,c_34831])).

tff(c_34834,plain,(
    k6_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13') = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_28746])).

tff(c_40753,plain,(
    ! [A_73130,B_73131,C_73132,D_73133] :
      ( k3_mcart_1(k5_mcart_1(A_73130,B_73131,C_73132,D_73133),k6_mcart_1(A_73130,B_73131,C_73132,D_73133),k7_mcart_1(A_73130,B_73131,C_73132,D_73133)) = D_73133
      | ~ m1_subset_1(D_73133,k3_zfmisc_1(A_73130,B_73131,C_73132))
      | k1_xboole_0 = C_73132
      | k1_xboole_0 = B_73131
      | k1_xboole_0 = A_73130 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40820,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13'),'#skF_13',k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13')) = '#skF_13'
    | ~ m1_subset_1('#skF_13',k3_zfmisc_1('#skF_10','#skF_11','#skF_12'))
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_34834,c_40753])).

tff(c_40824,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13'),'#skF_13',k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13')) = '#skF_13'
    | k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_40820])).

tff(c_40825,plain,(
    k3_mcart_1(k5_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13'),'#skF_13',k7_mcart_1('#skF_10','#skF_11','#skF_12','#skF_13')) = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_76,c_40824])).

tff(c_35366,plain,(
    ! [B_54681] :
      ( k2_tarski(B_54681,B_54681) = k1_xboole_0
      | '#skF_9'(k2_tarski(B_54681,B_54681)) = B_54681 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_159])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34897,plain,(
    ! [D_54592,A_54593,C_54594,E_54595] :
      ( ~ r2_hidden(D_54592,A_54593)
      | k3_mcart_1(C_54594,D_54592,E_54595) != '#skF_9'(A_54593)
      | k1_xboole_0 = A_54593 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34906,plain,(
    ! [C_54594,D_6,E_54595,A_1] :
      ( k3_mcart_1(C_54594,D_6,E_54595) != '#skF_9'(k2_tarski(A_1,D_6))
      | k2_tarski(A_1,D_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_34897])).

tff(c_35384,plain,(
    ! [C_54594,B_54681,E_54595] :
      ( k3_mcart_1(C_54594,B_54681,E_54595) != B_54681
      | k2_tarski(B_54681,B_54681) = k1_xboole_0
      | k2_tarski(B_54681,B_54681) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35366,c_34906])).

tff(c_40884,plain,(
    k2_tarski('#skF_13','#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40825,c_35384])).

tff(c_40922,plain,(
    r2_hidden('#skF_13',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40884,c_6])).

tff(c_41110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40036,c_40922])).

tff(c_41111,plain,(
    ! [D_6,A_70743] : r2_hidden(D_6,A_70743) ),
    inference(splitRight,[status(thm)],[c_40035])).

tff(c_41193,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41111,c_2])).

tff(c_61019,plain,(
    ! [D_83894,B_83895] : D_83894 = B_83895 ),
    inference(factorization,[status(thm),theory(equality)],[c_41193])).

tff(c_61507,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_61019,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:21:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.50/4.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.50/4.20  
% 11.50/4.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.50/4.20  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_9 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_2 > #skF_7 > #skF_3 > #skF_12
% 11.50/4.20  
% 11.50/4.20  %Foreground sorts:
% 11.50/4.20  
% 11.50/4.20  
% 11.50/4.20  %Background operators:
% 11.50/4.20  
% 11.50/4.20  
% 11.50/4.20  %Foreground operators:
% 11.50/4.20  tff('#skF_9', type, '#skF_9': $i > $i).
% 11.50/4.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.50/4.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.50/4.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.50/4.20  tff('#skF_11', type, '#skF_11': $i).
% 11.50/4.20  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 11.50/4.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.50/4.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.50/4.20  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 11.50/4.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.50/4.20  tff('#skF_10', type, '#skF_10': $i).
% 11.50/4.20  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 11.50/4.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.50/4.20  tff('#skF_13', type, '#skF_13': $i).
% 11.50/4.20  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.50/4.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.50/4.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.50/4.20  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 11.50/4.20  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 11.50/4.20  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 11.50/4.20  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 11.50/4.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.50/4.20  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 11.50/4.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.50/4.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.50/4.20  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 11.50/4.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.50/4.20  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 11.50/4.20  tff('#skF_12', type, '#skF_12': $i).
% 11.50/4.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.50/4.20  
% 11.70/4.22  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 11.70/4.22  tff(f_54, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.70/4.22  tff(f_48, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 11.70/4.22  tff(f_103, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 11.70/4.22  tff(f_127, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 11.70/4.22  tff(f_56, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 11.70/4.22  tff(f_67, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 11.70/4.22  tff(f_99, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 11.70/4.22  tff(f_83, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 11.70/4.22  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.70/4.22  tff(c_48, plain, (![A_43]: (k2_zfmisc_1(A_43, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.70/4.22  tff(c_34907, plain, (![E_54596, F_54597, A_54598, B_54599]: (r2_hidden(k4_tarski(E_54596, F_54597), k2_zfmisc_1(A_54598, B_54599)) | ~r2_hidden(F_54597, B_54599) | ~r2_hidden(E_54596, A_54598))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.70/4.22  tff(c_34927, plain, (![E_54603, F_54604, A_54605]: (r2_hidden(k4_tarski(E_54603, F_54604), k1_xboole_0) | ~r2_hidden(F_54604, k1_xboole_0) | ~r2_hidden(E_54603, A_54605))), inference(superposition, [status(thm), theory('equality')], [c_48, c_34907])).
% 11.70/4.22  tff(c_34939, plain, (![D_6, F_54604]: (r2_hidden(k4_tarski(D_6, F_54604), k1_xboole_0) | ~r2_hidden(F_54604, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_34927])).
% 11.70/4.22  tff(c_68, plain, (![A_75, B_76]: (k1_mcart_1(k4_tarski(A_75, B_76))=A_75)), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.70/4.22  tff(c_39475, plain, (![A_67839, B_67840, D_67841]: (k4_tarski('#skF_7'(A_67839, B_67840, k2_zfmisc_1(A_67839, B_67840), D_67841), '#skF_8'(A_67839, B_67840, k2_zfmisc_1(A_67839, B_67840), D_67841))=D_67841 | ~r2_hidden(D_67841, k2_zfmisc_1(A_67839, B_67840)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.70/4.22  tff(c_39604, plain, (![A_69203, B_69204, D_69205]: ('#skF_7'(A_69203, B_69204, k2_zfmisc_1(A_69203, B_69204), D_69205)=k1_mcart_1(D_69205) | ~r2_hidden(D_69205, k2_zfmisc_1(A_69203, B_69204)))), inference(superposition, [status(thm), theory('equality')], [c_39475, c_68])).
% 11.70/4.22  tff(c_39646, plain, (![A_43, D_69205]: ('#skF_7'(A_43, k1_xboole_0, k2_zfmisc_1(A_43, k1_xboole_0), D_69205)=k1_mcart_1(D_69205) | ~r2_hidden(D_69205, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_39604])).
% 11.70/4.22  tff(c_39667, plain, (![D_69374, A_69375]: (k1_mcart_1(D_69374)='#skF_7'(A_69375, k1_xboole_0, k1_xboole_0, D_69374) | ~r2_hidden(D_69374, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_39646])).
% 11.70/4.22  tff(c_39707, plain, (![D_6, F_54604, A_69375]: (k1_mcart_1(k4_tarski(D_6, F_54604))='#skF_7'(A_69375, k1_xboole_0, k1_xboole_0, k4_tarski(D_6, F_54604)) | ~r2_hidden(F_54604, k1_xboole_0))), inference(resolution, [status(thm)], [c_34939, c_39667])).
% 11.70/4.22  tff(c_39848, plain, (![A_70058, D_70059, F_70060]: ('#skF_7'(A_70058, k1_xboole_0, k1_xboole_0, k4_tarski(D_70059, F_70060))=D_70059 | ~r2_hidden(F_70060, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_39707])).
% 11.70/4.22  tff(c_34953, plain, (![A_54608, B_54609, D_54610]: (r2_hidden('#skF_7'(A_54608, B_54609, k2_zfmisc_1(A_54608, B_54609), D_54610), A_54608) | ~r2_hidden(D_54610, k2_zfmisc_1(A_54608, B_54609)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.70/4.22  tff(c_34967, plain, (![A_43, D_54610]: (r2_hidden('#skF_7'(A_43, k1_xboole_0, k1_xboole_0, D_54610), A_43) | ~r2_hidden(D_54610, k2_zfmisc_1(A_43, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_34953])).
% 11.70/4.22  tff(c_34975, plain, (![A_43, D_54610]: (r2_hidden('#skF_7'(A_43, k1_xboole_0, k1_xboole_0, D_54610), A_43) | ~r2_hidden(D_54610, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_34967])).
% 11.70/4.22  tff(c_40021, plain, (![D_70742, A_70743, F_70744]: (r2_hidden(D_70742, A_70743) | ~r2_hidden(k4_tarski(D_70742, F_70744), k1_xboole_0) | ~r2_hidden(F_70744, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_39848, c_34975])).
% 11.70/4.22  tff(c_40035, plain, (![D_6, A_70743, F_54604]: (r2_hidden(D_6, A_70743) | ~r2_hidden(F_54604, k1_xboole_0))), inference(resolution, [status(thm)], [c_34939, c_40021])).
% 11.70/4.22  tff(c_40036, plain, (![F_54604]: (~r2_hidden(F_54604, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_40035])).
% 11.70/4.22  tff(c_80, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.70/4.22  tff(c_78, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.70/4.22  tff(c_76, plain, (k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.70/4.22  tff(c_74, plain, (m1_subset_1('#skF_13', k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.70/4.22  tff(c_164, plain, (![A_100, B_101, C_102]: (k4_tarski(k4_tarski(A_100, B_101), C_102)=k3_mcart_1(A_100, B_101, C_102))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.70/4.22  tff(c_70, plain, (![A_75, B_76]: (k2_mcart_1(k4_tarski(A_75, B_76))=B_76)), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.70/4.22  tff(c_56, plain, (![B_54, C_55]: (k2_mcart_1(k4_tarski(B_54, C_55))!=k4_tarski(B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.70/4.22  tff(c_82, plain, (![B_54, C_55]: (k4_tarski(B_54, C_55)!=C_55)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_56])).
% 11.70/4.22  tff(c_179, plain, (![A_100, B_101, C_102]: (k3_mcart_1(A_100, B_101, C_102)!=C_102)), inference(superposition, [status(thm), theory('equality')], [c_164, c_82])).
% 11.70/4.22  tff(c_173, plain, (![A_100, B_101, C_102]: (k2_mcart_1(k3_mcart_1(A_100, B_101, C_102))=C_102)), inference(superposition, [status(thm), theory('equality')], [c_164, c_70])).
% 11.70/4.22  tff(c_50, plain, (![B_44]: (k2_zfmisc_1(k1_xboole_0, B_44)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.70/4.22  tff(c_372, plain, (![E_149, F_150, A_151, B_152]: (r2_hidden(k4_tarski(E_149, F_150), k2_zfmisc_1(A_151, B_152)) | ~r2_hidden(F_150, B_152) | ~r2_hidden(E_149, A_151))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.70/4.22  tff(c_476, plain, (![E_168, F_169, B_170]: (r2_hidden(k4_tarski(E_168, F_169), k1_xboole_0) | ~r2_hidden(F_169, B_170) | ~r2_hidden(E_168, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_372])).
% 11.70/4.22  tff(c_502, plain, (![E_168, D_6]: (r2_hidden(k4_tarski(E_168, D_6), k1_xboole_0) | ~r2_hidden(E_168, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_476])).
% 11.70/4.22  tff(c_5040, plain, (![A_13455, B_13456, D_13457]: (k4_tarski('#skF_7'(A_13455, B_13456, k2_zfmisc_1(A_13455, B_13456), D_13457), '#skF_8'(A_13455, B_13456, k2_zfmisc_1(A_13455, B_13456), D_13457))=D_13457 | ~r2_hidden(D_13457, k2_zfmisc_1(A_13455, B_13456)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.70/4.22  tff(c_5169, plain, (![A_14819, B_14820, D_14821]: ('#skF_8'(A_14819, B_14820, k2_zfmisc_1(A_14819, B_14820), D_14821)=k2_mcart_1(D_14821) | ~r2_hidden(D_14821, k2_zfmisc_1(A_14819, B_14820)))), inference(superposition, [status(thm), theory('equality')], [c_5040, c_70])).
% 11.70/4.22  tff(c_5213, plain, (![B_44, D_14821]: ('#skF_8'(k1_xboole_0, B_44, k2_zfmisc_1(k1_xboole_0, B_44), D_14821)=k2_mcart_1(D_14821) | ~r2_hidden(D_14821, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_5169])).
% 11.70/4.22  tff(c_5310, plain, (![D_15333, B_15334]: (k2_mcart_1(D_15333)='#skF_8'(k1_xboole_0, B_15334, k1_xboole_0, D_15333) | ~r2_hidden(D_15333, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5213])).
% 11.70/4.22  tff(c_5338, plain, (![E_168, D_6, B_15334]: (k2_mcart_1(k4_tarski(E_168, D_6))='#skF_8'(k1_xboole_0, B_15334, k1_xboole_0, k4_tarski(E_168, D_6)) | ~r2_hidden(E_168, k1_xboole_0))), inference(resolution, [status(thm)], [c_502, c_5310])).
% 11.70/4.22  tff(c_5418, plain, (![B_15674, E_15675, D_15676]: ('#skF_8'(k1_xboole_0, B_15674, k1_xboole_0, k4_tarski(E_15675, D_15676))=D_15676 | ~r2_hidden(E_15675, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5338])).
% 11.70/4.22  tff(c_517, plain, (![A_173, B_174, D_175]: (r2_hidden('#skF_8'(A_173, B_174, k2_zfmisc_1(A_173, B_174), D_175), B_174) | ~r2_hidden(D_175, k2_zfmisc_1(A_173, B_174)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.70/4.22  tff(c_531, plain, (![A_43, D_175]: (r2_hidden('#skF_8'(A_43, k1_xboole_0, k1_xboole_0, D_175), k1_xboole_0) | ~r2_hidden(D_175, k2_zfmisc_1(A_43, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_517])).
% 11.70/4.22  tff(c_539, plain, (![A_43, D_175]: (r2_hidden('#skF_8'(A_43, k1_xboole_0, k1_xboole_0, D_175), k1_xboole_0) | ~r2_hidden(D_175, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_531])).
% 11.70/4.22  tff(c_5601, plain, (![D_16358, E_16359]: (r2_hidden(D_16358, k1_xboole_0) | ~r2_hidden(k4_tarski(E_16359, D_16358), k1_xboole_0) | ~r2_hidden(E_16359, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5418, c_539])).
% 11.70/4.22  tff(c_5618, plain, (![D_6, E_168]: (r2_hidden(D_6, k1_xboole_0) | ~r2_hidden(E_168, k1_xboole_0))), inference(resolution, [status(thm)], [c_502, c_5601])).
% 11.70/4.22  tff(c_5620, plain, (![E_168]: (~r2_hidden(E_168, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_5618])).
% 11.70/4.22  tff(c_72, plain, (k7_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13')='#skF_13' | k6_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13')='#skF_13' | k5_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13')='#skF_13'), inference(cnfTransformation, [status(thm)], [f_127])).
% 11.70/4.22  tff(c_201, plain, (k5_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13')='#skF_13'), inference(splitLeft, [status(thm)], [c_72])).
% 11.70/4.22  tff(c_6336, plain, (![A_18745, B_18746, C_18747, D_18748]: (k3_mcart_1(k5_mcart_1(A_18745, B_18746, C_18747, D_18748), k6_mcart_1(A_18745, B_18746, C_18747, D_18748), k7_mcart_1(A_18745, B_18746, C_18747, D_18748))=D_18748 | ~m1_subset_1(D_18748, k3_zfmisc_1(A_18745, B_18746, C_18747)) | k1_xboole_0=C_18747 | k1_xboole_0=B_18746 | k1_xboole_0=A_18745)), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.70/4.22  tff(c_6405, plain, (k3_mcart_1('#skF_13', k6_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'), k7_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'))='#skF_13' | ~m1_subset_1('#skF_13', k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_201, c_6336])).
% 11.70/4.22  tff(c_6409, plain, (k3_mcart_1('#skF_13', k6_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'), k7_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'))='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6405])).
% 11.70/4.22  tff(c_6410, plain, (k3_mcart_1('#skF_13', k6_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'), k7_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'))='#skF_13'), inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_76, c_6409])).
% 11.70/4.22  tff(c_60, plain, (![A_56]: (r2_hidden('#skF_9'(A_56), A_56) | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.70/4.22  tff(c_148, plain, (![D_97, B_98, A_99]: (D_97=B_98 | D_97=A_99 | ~r2_hidden(D_97, k2_tarski(A_99, B_98)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.70/4.22  tff(c_159, plain, (![A_99, B_98]: ('#skF_9'(k2_tarski(A_99, B_98))=B_98 | '#skF_9'(k2_tarski(A_99, B_98))=A_99 | k2_tarski(A_99, B_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_148])).
% 11.70/4.22  tff(c_746, plain, (![B_214]: (k2_tarski(B_214, B_214)=k1_xboole_0 | '#skF_9'(k2_tarski(B_214, B_214))=B_214)), inference(factorization, [status(thm), theory('equality')], [c_159])).
% 11.70/4.22  tff(c_257, plain, (![C_120, A_121, D_122, E_123]: (~r2_hidden(C_120, A_121) | k3_mcart_1(C_120, D_122, E_123)!='#skF_9'(A_121) | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.70/4.22  tff(c_265, plain, (![D_6, D_122, E_123, B_2]: (k3_mcart_1(D_6, D_122, E_123)!='#skF_9'(k2_tarski(D_6, B_2)) | k2_tarski(D_6, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_257])).
% 11.70/4.22  tff(c_761, plain, (![B_214, D_122, E_123]: (k3_mcart_1(B_214, D_122, E_123)!=B_214 | k2_tarski(B_214, B_214)=k1_xboole_0 | k2_tarski(B_214, B_214)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_746, c_265])).
% 11.70/4.22  tff(c_6471, plain, (k2_tarski('#skF_13', '#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6410, c_761])).
% 11.70/4.22  tff(c_6509, plain, (r2_hidden('#skF_13', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6471, c_6])).
% 11.70/4.22  tff(c_6697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5620, c_6509])).
% 11.70/4.22  tff(c_6698, plain, (![D_6]: (r2_hidden(D_6, k1_xboole_0))), inference(splitRight, [status(thm)], [c_5618])).
% 11.70/4.22  tff(c_5231, plain, (![D_14821, B_44]: (k2_mcart_1(D_14821)='#skF_8'(k1_xboole_0, B_44, k1_xboole_0, D_14821) | ~r2_hidden(D_14821, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5213])).
% 11.70/4.22  tff(c_6843, plain, (![D_20786, B_20787]: (k2_mcart_1(D_20786)='#skF_8'(k1_xboole_0, B_20787, k1_xboole_0, D_20786))), inference(demodulation, [status(thm), theory('equality')], [c_6698, c_5231])).
% 11.70/4.22  tff(c_534, plain, (![B_44, D_175]: (r2_hidden('#skF_8'(k1_xboole_0, B_44, k1_xboole_0, D_175), B_44) | ~r2_hidden(D_175, k2_zfmisc_1(k1_xboole_0, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_517])).
% 11.70/4.22  tff(c_540, plain, (![B_44, D_175]: (r2_hidden('#skF_8'(k1_xboole_0, B_44, k1_xboole_0, D_175), B_44) | ~r2_hidden(D_175, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_534])).
% 11.70/4.22  tff(c_6733, plain, (![B_44, D_175]: (r2_hidden('#skF_8'(k1_xboole_0, B_44, k1_xboole_0, D_175), B_44))), inference(demodulation, [status(thm), theory('equality')], [c_6698, c_540])).
% 11.70/4.22  tff(c_6901, plain, (![D_21296, B_21297]: (r2_hidden(k2_mcart_1(D_21296), B_21297))), inference(superposition, [status(thm), theory('equality')], [c_6843, c_6733])).
% 11.70/4.22  tff(c_6919, plain, (![C_102, B_21297]: (r2_hidden(C_102, B_21297))), inference(superposition, [status(thm), theory('equality')], [c_173, c_6901])).
% 11.70/4.22  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.70/4.22  tff(c_6968, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_6919, c_2])).
% 11.70/4.22  tff(c_28245, plain, (![D_32671, B_32672]: (D_32671=B_32672)), inference(factorization, [status(thm), theory('equality')], [c_6968])).
% 11.70/4.22  tff(c_5115, plain, (![A_13626, B_13627, D_13628]: ('#skF_8'(A_13626, B_13627, k2_zfmisc_1(A_13626, B_13627), D_13628)!=D_13628 | ~r2_hidden(D_13628, k2_zfmisc_1(A_13626, B_13627)))), inference(superposition, [status(thm), theory('equality')], [c_5040, c_82])).
% 11.70/4.22  tff(c_5127, plain, (![B_44, D_13628]: ('#skF_8'(k1_xboole_0, B_44, k1_xboole_0, D_13628)!=D_13628 | ~r2_hidden(D_13628, k2_zfmisc_1(k1_xboole_0, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_5115])).
% 11.70/4.22  tff(c_5130, plain, (![B_44, D_13628]: ('#skF_8'(k1_xboole_0, B_44, k1_xboole_0, D_13628)!=D_13628 | ~r2_hidden(D_13628, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5127])).
% 11.70/4.22  tff(c_6718, plain, (![B_44, D_13628]: ('#skF_8'(k1_xboole_0, B_44, k1_xboole_0, D_13628)!=D_13628)), inference(demodulation, [status(thm), theory('equality')], [c_6698, c_5130])).
% 11.70/4.22  tff(c_6855, plain, (![D_20786]: (k2_mcart_1(D_20786)!=D_20786)), inference(superposition, [status(thm), theory('equality')], [c_6843, c_6718])).
% 11.70/4.22  tff(c_28745, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_28245, c_6855])).
% 11.70/4.22  tff(c_28746, plain, (k6_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13')='#skF_13' | k7_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13')='#skF_13'), inference(splitRight, [status(thm)], [c_72])).
% 11.70/4.22  tff(c_28792, plain, (k7_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13')='#skF_13'), inference(splitLeft, [status(thm)], [c_28746])).
% 11.70/4.22  tff(c_34751, plain, (![A_54407, B_54408, C_54409, D_54410]: (k3_mcart_1(k5_mcart_1(A_54407, B_54408, C_54409, D_54410), k6_mcart_1(A_54407, B_54408, C_54409, D_54410), k7_mcart_1(A_54407, B_54408, C_54409, D_54410))=D_54410 | ~m1_subset_1(D_54410, k3_zfmisc_1(A_54407, B_54408, C_54409)) | k1_xboole_0=C_54409 | k1_xboole_0=B_54408 | k1_xboole_0=A_54407)), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.70/4.22  tff(c_34827, plain, (k3_mcart_1(k5_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'), k6_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'), '#skF_13')='#skF_13' | ~m1_subset_1('#skF_13', k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_28792, c_34751])).
% 11.70/4.22  tff(c_34831, plain, (k3_mcart_1(k5_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'), k6_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'), '#skF_13')='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_34827])).
% 11.70/4.22  tff(c_34833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_76, c_179, c_34831])).
% 11.70/4.22  tff(c_34834, plain, (k6_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13')='#skF_13'), inference(splitRight, [status(thm)], [c_28746])).
% 11.70/4.22  tff(c_40753, plain, (![A_73130, B_73131, C_73132, D_73133]: (k3_mcart_1(k5_mcart_1(A_73130, B_73131, C_73132, D_73133), k6_mcart_1(A_73130, B_73131, C_73132, D_73133), k7_mcart_1(A_73130, B_73131, C_73132, D_73133))=D_73133 | ~m1_subset_1(D_73133, k3_zfmisc_1(A_73130, B_73131, C_73132)) | k1_xboole_0=C_73132 | k1_xboole_0=B_73131 | k1_xboole_0=A_73130)), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.70/4.22  tff(c_40820, plain, (k3_mcart_1(k5_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'), '#skF_13', k7_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'))='#skF_13' | ~m1_subset_1('#skF_13', k3_zfmisc_1('#skF_10', '#skF_11', '#skF_12')) | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_34834, c_40753])).
% 11.70/4.22  tff(c_40824, plain, (k3_mcart_1(k5_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'), '#skF_13', k7_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'))='#skF_13' | k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_40820])).
% 11.70/4.22  tff(c_40825, plain, (k3_mcart_1(k5_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'), '#skF_13', k7_mcart_1('#skF_10', '#skF_11', '#skF_12', '#skF_13'))='#skF_13'), inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_76, c_40824])).
% 11.70/4.22  tff(c_35366, plain, (![B_54681]: (k2_tarski(B_54681, B_54681)=k1_xboole_0 | '#skF_9'(k2_tarski(B_54681, B_54681))=B_54681)), inference(factorization, [status(thm), theory('equality')], [c_159])).
% 11.70/4.22  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.70/4.22  tff(c_34897, plain, (![D_54592, A_54593, C_54594, E_54595]: (~r2_hidden(D_54592, A_54593) | k3_mcart_1(C_54594, D_54592, E_54595)!='#skF_9'(A_54593) | k1_xboole_0=A_54593)), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.70/4.22  tff(c_34906, plain, (![C_54594, D_6, E_54595, A_1]: (k3_mcart_1(C_54594, D_6, E_54595)!='#skF_9'(k2_tarski(A_1, D_6)) | k2_tarski(A_1, D_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_34897])).
% 11.70/4.22  tff(c_35384, plain, (![C_54594, B_54681, E_54595]: (k3_mcart_1(C_54594, B_54681, E_54595)!=B_54681 | k2_tarski(B_54681, B_54681)=k1_xboole_0 | k2_tarski(B_54681, B_54681)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_35366, c_34906])).
% 11.70/4.22  tff(c_40884, plain, (k2_tarski('#skF_13', '#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_40825, c_35384])).
% 11.70/4.22  tff(c_40922, plain, (r2_hidden('#skF_13', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40884, c_6])).
% 11.70/4.22  tff(c_41110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40036, c_40922])).
% 11.70/4.22  tff(c_41111, plain, (![D_6, A_70743]: (r2_hidden(D_6, A_70743))), inference(splitRight, [status(thm)], [c_40035])).
% 11.70/4.22  tff(c_41193, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_41111, c_2])).
% 11.70/4.22  tff(c_61019, plain, (![D_83894, B_83895]: (D_83894=B_83895)), inference(factorization, [status(thm), theory('equality')], [c_41193])).
% 11.70/4.22  tff(c_61507, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_61019, c_179])).
% 11.70/4.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.70/4.22  
% 11.70/4.22  Inference rules
% 11.70/4.22  ----------------------
% 11.70/4.22  #Ref     : 0
% 11.70/4.22  #Sup     : 8835
% 11.70/4.22  #Fact    : 38
% 11.70/4.22  #Define  : 0
% 11.70/4.22  #Split   : 5
% 11.70/4.22  #Chain   : 0
% 11.70/4.22  #Close   : 0
% 11.70/4.22  
% 11.70/4.22  Ordering : KBO
% 11.70/4.22  
% 11.70/4.22  Simplification rules
% 11.70/4.22  ----------------------
% 11.70/4.22  #Subsume      : 4070
% 11.70/4.22  #Demod        : 2106
% 11.70/4.22  #Tautology    : 548
% 11.70/4.22  #SimpNegUnit  : 201
% 11.70/4.22  #BackRed      : 51
% 11.70/4.22  
% 11.70/4.22  #Partial instantiations: 37650
% 11.70/4.22  #Strategies tried      : 1
% 11.70/4.22  
% 11.70/4.22  Timing (in seconds)
% 11.70/4.22  ----------------------
% 11.70/4.23  Preprocessing        : 0.39
% 11.70/4.23  Parsing              : 0.20
% 11.70/4.23  CNF conversion       : 0.03
% 11.70/4.23  Main loop            : 2.98
% 11.70/4.23  Inferencing          : 1.48
% 11.70/4.23  Reduction            : 0.76
% 11.70/4.23  Demodulation         : 0.49
% 11.70/4.23  BG Simplification    : 0.14
% 11.70/4.23  Subsumption          : 0.43
% 11.70/4.23  Abstraction          : 0.17
% 11.70/4.23  MUC search           : 0.00
% 11.70/4.23  Cooper               : 0.00
% 11.70/4.23  Total                : 3.41
% 11.70/4.23  Index Insertion      : 0.00
% 11.70/4.23  Index Deletion       : 0.00
% 11.70/4.23  Index Matching       : 0.00
% 11.70/4.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
