%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:43 EST 2020

% Result     : Theorem 13.79s
% Output     : CNFRefutation 13.95s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 373 expanded)
%              Number of leaves         :   35 ( 143 expanded)
%              Depth                    :   11
%              Number of atoms          :  219 (1031 expanded)
%              Number of equality atoms :  145 ( 661 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_77,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_109,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_68,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_22,plain,(
    ! [D_12,A_7] : r2_hidden(D_12,k2_tarski(A_7,D_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_5'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_98,plain,(
    ! [D_64,A_65,B_66] :
      ( r2_hidden(D_64,A_65)
      | ~ r2_hidden(D_64,k4_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_236,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_107,B_108)),A_107)
      | k4_xboole_0(A_107,B_108) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_98])).

tff(c_112,plain,(
    ! [D_67,B_68,A_69] :
      ( ~ r2_hidden(D_67,B_68)
      | ~ r2_hidden(D_67,k4_xboole_0(A_69,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [A_69,B_68] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_69,B_68)),B_68)
      | k4_xboole_0(A_69,B_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_112])).

tff(c_293,plain,(
    ! [A_112] : k4_xboole_0(A_112,A_112) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_236,c_125])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_336,plain,(
    ! [D_115,A_116] :
      ( ~ r2_hidden(D_115,A_116)
      | ~ r2_hidden(D_115,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_4])).

tff(c_353,plain,(
    ! [D_12] : ~ r2_hidden(D_12,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_336])).

tff(c_42,plain,(
    ! [A_15,B_16,C_17] :
      ( k4_xboole_0(k2_tarski(A_15,B_16),C_17) = k2_tarski(A_15,B_16)
      | r2_hidden(B_16,C_17)
      | r2_hidden(A_15,C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [D_12,B_8] : r2_hidden(D_12,k2_tarski(D_12,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,
    ( k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10'
    | k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10'
    | k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_88,plain,(
    k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_20097,plain,(
    ! [A_10683,B_10684,C_10685,D_10686] :
      ( k3_mcart_1(k5_mcart_1(A_10683,B_10684,C_10685,D_10686),k6_mcart_1(A_10683,B_10684,C_10685,D_10686),k7_mcart_1(A_10683,B_10684,C_10685,D_10686)) = D_10686
      | ~ m1_subset_1(D_10686,k3_zfmisc_1(A_10683,B_10684,C_10685))
      | k1_xboole_0 = C_10685
      | k1_xboole_0 = B_10684
      | k1_xboole_0 = A_10683 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20139,plain,
    ( k3_mcart_1('#skF_10',k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_20097])).

tff(c_20143,plain,
    ( k3_mcart_1('#skF_10',k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10')) = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_20139])).

tff(c_20144,plain,(
    k3_mcart_1('#skF_10',k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_70,c_20143])).

tff(c_40,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,k1_tarski(B_14)) = A_13
      | r2_hidden(B_14,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_217,plain,(
    ! [B_99,C_100,A_101] :
      ( ~ r2_hidden(B_99,C_100)
      | k4_xboole_0(k2_tarski(A_101,B_99),C_100) != k2_tarski(A_101,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_223,plain,(
    ! [B_102,B_103,A_104] :
      ( ~ r2_hidden(B_102,k1_tarski(B_103))
      | r2_hidden(B_103,k2_tarski(A_104,B_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_217])).

tff(c_712,plain,(
    ! [B_183,A_184] :
      ( r2_hidden(B_183,k2_tarski(A_184,'#skF_5'(k1_tarski(B_183))))
      | k1_tarski(B_183) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_223])).

tff(c_20,plain,(
    ! [D_12,B_8,A_7] :
      ( D_12 = B_8
      | D_12 = A_7
      | ~ r2_hidden(D_12,k2_tarski(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_736,plain,(
    ! [B_183,A_184] :
      ( '#skF_5'(k1_tarski(B_183)) = B_183
      | B_183 = A_184
      | k1_tarski(B_183) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_712,c_20])).

tff(c_754,plain,(
    ! [B_183] :
      ( k1_tarski(B_183) = k1_xboole_0
      | '#skF_5'(k1_tarski(B_183)) = B_183 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_736])).

tff(c_322,plain,(
    ! [B_14] :
      ( k1_tarski(B_14) = k1_xboole_0
      | r2_hidden(B_14,k1_tarski(B_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_40])).

tff(c_480,plain,(
    ! [C_132,A_133,D_134,E_135] :
      ( ~ r2_hidden(C_132,A_133)
      | k3_mcart_1(C_132,D_134,E_135) != '#skF_5'(A_133)
      | k1_xboole_0 = A_133 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_19675,plain,(
    ! [B_10613,D_10614,E_10615] :
      ( k3_mcart_1(B_10613,D_10614,E_10615) != '#skF_5'(k1_tarski(B_10613))
      | k1_tarski(B_10613) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_322,c_480])).

tff(c_19678,plain,(
    ! [B_183,D_10614,E_10615] :
      ( k3_mcart_1(B_183,D_10614,E_10615) != B_183
      | k1_tarski(B_183) = k1_xboole_0
      | k1_tarski(B_183) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_754,c_19675])).

tff(c_20184,plain,(
    k1_tarski('#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20144,c_19678])).

tff(c_38,plain,(
    ! [B_14,A_13] :
      ( ~ r2_hidden(B_14,A_13)
      | k4_xboole_0(A_13,k1_tarski(B_14)) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20267,plain,(
    ! [A_10700] :
      ( ~ r2_hidden('#skF_10',A_10700)
      | k4_xboole_0(A_10700,k1_xboole_0) != A_10700 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20184,c_38])).

tff(c_20384,plain,(
    ! [B_10706] : k4_xboole_0(k2_tarski('#skF_10',B_10706),k1_xboole_0) != k2_tarski('#skF_10',B_10706) ),
    inference(resolution,[status(thm)],[c_24,c_20267])).

tff(c_20388,plain,(
    ! [B_16] :
      ( r2_hidden(B_16,k1_xboole_0)
      | r2_hidden('#skF_10',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_20384])).

tff(c_20392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_353,c_20388])).

tff(c_20393,plain,
    ( k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10'
    | k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_20395,plain,(
    k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_20393])).

tff(c_51233,plain,(
    ! [A_27858,B_27859,C_27860,D_27861] :
      ( k3_mcart_1(k5_mcart_1(A_27858,B_27859,C_27860,D_27861),k6_mcart_1(A_27858,B_27859,C_27860,D_27861),k7_mcart_1(A_27858,B_27859,C_27860,D_27861)) = D_27861
      | ~ m1_subset_1(D_27861,k3_zfmisc_1(A_27858,B_27859,C_27860))
      | k1_xboole_0 = C_27860
      | k1_xboole_0 = B_27859
      | k1_xboole_0 = A_27858 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52064,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_10') = '#skF_10'
    | ~ m1_subset_1('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_20395,c_51233])).

tff(c_52092,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_10') = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_52064])).

tff(c_52093,plain,(
    k3_mcart_1(k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_10') = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_70,c_52092])).

tff(c_48,plain,(
    ! [A_18,B_19,C_20] : k4_tarski(k4_tarski(A_18,B_19),C_20) = k3_mcart_1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20405,plain,(
    ! [D_10709,A_10710,B_10711] :
      ( r2_hidden(D_10709,A_10710)
      | ~ r2_hidden(D_10709,k4_xboole_0(A_10710,B_10711)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20558,plain,(
    ! [A_10766,B_10767] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_10766,B_10767)),A_10766)
      | k4_xboole_0(A_10766,B_10767) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_20405])).

tff(c_20419,plain,(
    ! [D_10712,B_10713,A_10714] :
      ( ~ r2_hidden(D_10712,B_10713)
      | ~ r2_hidden(D_10712,k4_xboole_0(A_10714,B_10713)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20432,plain,(
    ! [A_10714,B_10713] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_10714,B_10713)),B_10713)
      | k4_xboole_0(A_10714,B_10713) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_20419])).

tff(c_20587,plain,(
    ! [A_10766] : k4_xboole_0(A_10766,A_10766) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20558,c_20432])).

tff(c_20643,plain,(
    ! [B_10771,C_10772,A_10773] :
      ( ~ r2_hidden(B_10771,C_10772)
      | k4_xboole_0(k2_tarski(A_10773,B_10771),C_10772) != k2_tarski(A_10773,B_10771) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20647,plain,(
    ! [B_10771,A_10773] :
      ( ~ r2_hidden(B_10771,k2_tarski(A_10773,B_10771))
      | k2_tarski(A_10773,B_10771) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20587,c_20643])).

tff(c_20653,plain,(
    ! [A_10773,B_10771] : k2_tarski(A_10773,B_10771) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20647])).

tff(c_20484,plain,(
    ! [D_10724,A_10725,C_10726] :
      ( ~ r2_hidden(D_10724,A_10725)
      | k4_tarski(C_10726,D_10724) != '#skF_6'(A_10725)
      | k1_xboole_0 = A_10725 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_20496,plain,(
    ! [C_10726,D_12,B_8] :
      ( k4_tarski(C_10726,D_12) != '#skF_6'(k2_tarski(D_12,B_8))
      | k2_tarski(D_12,B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_20484])).

tff(c_53519,plain,(
    ! [C_29238,D_29239,B_29240] : k4_tarski(C_29238,D_29239) != '#skF_6'(k2_tarski(D_29239,B_29240)) ),
    inference(negUnitSimplification,[status(thm)],[c_20653,c_20496])).

tff(c_53798,plain,(
    ! [A_29364,B_29365,C_29366,B_29367] : k3_mcart_1(A_29364,B_29365,C_29366) != '#skF_6'(k2_tarski(C_29366,B_29367)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_53519])).

tff(c_53801,plain,(
    ! [B_29367] : '#skF_6'(k2_tarski('#skF_10',B_29367)) != '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_52093,c_53798])).

tff(c_60,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_6'(A_43),A_43)
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_20448,plain,(
    ! [D_10718,B_10719,A_10720] :
      ( D_10718 = B_10719
      | D_10718 = A_10720
      | ~ r2_hidden(D_10718,k2_tarski(A_10720,B_10719)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20463,plain,(
    ! [A_10720,B_10719] :
      ( '#skF_6'(k2_tarski(A_10720,B_10719)) = B_10719
      | '#skF_6'(k2_tarski(A_10720,B_10719)) = A_10720
      | k2_tarski(A_10720,B_10719) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60,c_20448])).

tff(c_54182,plain,(
    ! [A_29395,B_29396] :
      ( '#skF_6'(k2_tarski(A_29395,B_29396)) = B_29396
      | '#skF_6'(k2_tarski(A_29395,B_29396)) = A_29395 ) ),
    inference(negUnitSimplification,[status(thm)],[c_20653,c_20463])).

tff(c_54199,plain,(
    ! [B_29396] :
      ( B_29396 != '#skF_10'
      | '#skF_6'(k2_tarski('#skF_10',B_29396)) = '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54182,c_53801])).

tff(c_54285,plain,(
    ! [B_29396] : B_29396 != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_53801,c_54199])).

tff(c_54303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54285,c_52093])).

tff(c_54304,plain,(
    k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_20393])).

tff(c_89578,plain,(
    ! [A_49510,B_49511,C_49512,D_49513] :
      ( k3_mcart_1(k5_mcart_1(A_49510,B_49511,C_49512,D_49513),k6_mcart_1(A_49510,B_49511,C_49512,D_49513),k7_mcart_1(A_49510,B_49511,C_49512,D_49513)) = D_49513
      | ~ m1_subset_1(D_49513,k3_zfmisc_1(A_49510,B_49511,C_49512))
      | k1_xboole_0 = C_49512
      | k1_xboole_0 = B_49511
      | k1_xboole_0 = A_49510 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_90415,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_10',k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_54304,c_89578])).

tff(c_90443,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_10',k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10')) = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_90415])).

tff(c_90444,plain,(
    k3_mcart_1(k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_10',k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_70,c_90443])).

tff(c_54310,plain,(
    ! [D_29397,A_29398,B_29399] :
      ( r2_hidden(D_29397,A_29398)
      | ~ r2_hidden(D_29397,k4_xboole_0(A_29398,B_29399)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54457,plain,(
    ! [A_29444,B_29445] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_29444,B_29445)),A_29444)
      | k4_xboole_0(A_29444,B_29445) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_54310])).

tff(c_54324,plain,(
    ! [D_29400,B_29401,A_29402] :
      ( ~ r2_hidden(D_29400,B_29401)
      | ~ r2_hidden(D_29400,k4_xboole_0(A_29402,B_29401)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54337,plain,(
    ! [A_29402,B_29401] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_29402,B_29401)),B_29401)
      | k4_xboole_0(A_29402,B_29401) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_54324])).

tff(c_54491,plain,(
    ! [A_29446] : k4_xboole_0(A_29446,A_29446) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54457,c_54337])).

tff(c_46,plain,(
    ! [A_15,C_17,B_16] :
      ( ~ r2_hidden(A_15,C_17)
      | k4_xboole_0(k2_tarski(A_15,B_16),C_17) != k2_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54500,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden(A_15,k2_tarski(A_15,B_16))
      | k2_tarski(A_15,B_16) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54491,c_46])).

tff(c_54530,plain,(
    ! [A_15,B_16] : k2_tarski(A_15,B_16) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_54500])).

tff(c_54534,plain,(
    ! [D_29447,A_29448,C_29449,E_29450] :
      ( ~ r2_hidden(D_29447,A_29448)
      | k3_mcart_1(C_29449,D_29447,E_29450) != '#skF_5'(A_29448)
      | k1_xboole_0 = A_29448 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_54549,plain,(
    ! [C_29449,D_12,E_29450,B_8] :
      ( k3_mcart_1(C_29449,D_12,E_29450) != '#skF_5'(k2_tarski(D_12,B_8))
      | k2_tarski(D_12,B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_54534])).

tff(c_92085,plain,(
    ! [C_50827,D_50828,E_50829,B_50830] : k3_mcart_1(C_50827,D_50828,E_50829) != '#skF_5'(k2_tarski(D_50828,B_50830)) ),
    inference(negUnitSimplification,[status(thm)],[c_54530,c_54549])).

tff(c_92088,plain,(
    ! [B_50830] : '#skF_5'(k2_tarski('#skF_10',B_50830)) != '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_90444,c_92085])).

tff(c_54343,plain,(
    ! [D_29405,B_29406,A_29407] :
      ( D_29405 = B_29406
      | D_29405 = A_29407
      | ~ r2_hidden(D_29405,k2_tarski(A_29407,B_29406)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54359,plain,(
    ! [A_29407,B_29406] :
      ( '#skF_5'(k2_tarski(A_29407,B_29406)) = B_29406
      | '#skF_5'(k2_tarski(A_29407,B_29406)) = A_29407
      | k2_tarski(A_29407,B_29406) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_54343])).

tff(c_92499,plain,(
    ! [A_50872,B_50873] :
      ( '#skF_5'(k2_tarski(A_50872,B_50873)) = B_50873
      | '#skF_5'(k2_tarski(A_50872,B_50873)) = A_50872 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54530,c_54359])).

tff(c_92517,plain,(
    ! [B_50873] :
      ( B_50873 != '#skF_10'
      | '#skF_5'(k2_tarski('#skF_10',B_50873)) = '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92499,c_92088])).

tff(c_92617,plain,(
    ! [B_50873] : B_50873 != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_92088,c_92517])).

tff(c_92640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92617,c_90444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.79/5.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.79/6.00  
% 13.79/6.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.95/6.01  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_6
% 13.95/6.01  
% 13.95/6.01  %Foreground sorts:
% 13.95/6.01  
% 13.95/6.01  
% 13.95/6.01  %Background operators:
% 13.95/6.01  
% 13.95/6.01  
% 13.95/6.01  %Foreground operators:
% 13.95/6.01  tff('#skF_5', type, '#skF_5': $i > $i).
% 13.95/6.01  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.95/6.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.95/6.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.95/6.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.95/6.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.95/6.01  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.95/6.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.95/6.01  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 13.95/6.01  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.95/6.01  tff('#skF_7', type, '#skF_7': $i).
% 13.95/6.01  tff('#skF_10', type, '#skF_10': $i).
% 13.95/6.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.95/6.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.95/6.01  tff('#skF_9', type, '#skF_9': $i).
% 13.95/6.01  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 13.95/6.01  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 13.95/6.01  tff('#skF_8', type, '#skF_8': $i).
% 13.95/6.01  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 13.95/6.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.95/6.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.95/6.01  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.95/6.01  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 13.95/6.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.95/6.01  tff('#skF_6', type, '#skF_6': $i > $i).
% 13.95/6.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.95/6.01  
% 13.95/6.03  tff(f_133, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 13.95/6.03  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 13.95/6.03  tff(f_77, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 13.95/6.03  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.95/6.03  tff(f_57, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 13.95/6.03  tff(f_93, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 13.95/6.03  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 13.95/6.03  tff(f_59, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 13.95/6.03  tff(f_109, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 13.95/6.03  tff(c_74, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.95/6.03  tff(c_72, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.95/6.03  tff(c_70, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.95/6.03  tff(c_68, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.95/6.03  tff(c_22, plain, (![D_12, A_7]: (r2_hidden(D_12, k2_tarski(A_7, D_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.95/6.03  tff(c_52, plain, (![A_24]: (r2_hidden('#skF_5'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.95/6.03  tff(c_98, plain, (![D_64, A_65, B_66]: (r2_hidden(D_64, A_65) | ~r2_hidden(D_64, k4_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.95/6.03  tff(c_236, plain, (![A_107, B_108]: (r2_hidden('#skF_5'(k4_xboole_0(A_107, B_108)), A_107) | k4_xboole_0(A_107, B_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_98])).
% 13.95/6.03  tff(c_112, plain, (![D_67, B_68, A_69]: (~r2_hidden(D_67, B_68) | ~r2_hidden(D_67, k4_xboole_0(A_69, B_68)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.95/6.03  tff(c_125, plain, (![A_69, B_68]: (~r2_hidden('#skF_5'(k4_xboole_0(A_69, B_68)), B_68) | k4_xboole_0(A_69, B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_112])).
% 13.95/6.03  tff(c_293, plain, (![A_112]: (k4_xboole_0(A_112, A_112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_236, c_125])).
% 13.95/6.03  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.95/6.03  tff(c_336, plain, (![D_115, A_116]: (~r2_hidden(D_115, A_116) | ~r2_hidden(D_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_293, c_4])).
% 13.95/6.03  tff(c_353, plain, (![D_12]: (~r2_hidden(D_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_336])).
% 13.95/6.03  tff(c_42, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k2_tarski(A_15, B_16), C_17)=k2_tarski(A_15, B_16) | r2_hidden(B_16, C_17) | r2_hidden(A_15, C_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.95/6.03  tff(c_24, plain, (![D_12, B_8]: (r2_hidden(D_12, k2_tarski(D_12, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.95/6.03  tff(c_66, plain, (k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10' | k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10' | k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.95/6.03  tff(c_88, plain, (k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(splitLeft, [status(thm)], [c_66])).
% 13.95/6.03  tff(c_20097, plain, (![A_10683, B_10684, C_10685, D_10686]: (k3_mcart_1(k5_mcart_1(A_10683, B_10684, C_10685, D_10686), k6_mcart_1(A_10683, B_10684, C_10685, D_10686), k7_mcart_1(A_10683, B_10684, C_10685, D_10686))=D_10686 | ~m1_subset_1(D_10686, k3_zfmisc_1(A_10683, B_10684, C_10685)) | k1_xboole_0=C_10685 | k1_xboole_0=B_10684 | k1_xboole_0=A_10683)), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.95/6.03  tff(c_20139, plain, (k3_mcart_1('#skF_10', k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_88, c_20097])).
% 13.95/6.03  tff(c_20143, plain, (k3_mcart_1('#skF_10', k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_20139])).
% 13.95/6.03  tff(c_20144, plain, (k3_mcart_1('#skF_10', k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_70, c_20143])).
% 13.95/6.03  tff(c_40, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k1_tarski(B_14))=A_13 | r2_hidden(B_14, A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.95/6.03  tff(c_217, plain, (![B_99, C_100, A_101]: (~r2_hidden(B_99, C_100) | k4_xboole_0(k2_tarski(A_101, B_99), C_100)!=k2_tarski(A_101, B_99))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.95/6.03  tff(c_223, plain, (![B_102, B_103, A_104]: (~r2_hidden(B_102, k1_tarski(B_103)) | r2_hidden(B_103, k2_tarski(A_104, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_217])).
% 13.95/6.03  tff(c_712, plain, (![B_183, A_184]: (r2_hidden(B_183, k2_tarski(A_184, '#skF_5'(k1_tarski(B_183)))) | k1_tarski(B_183)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_223])).
% 13.95/6.03  tff(c_20, plain, (![D_12, B_8, A_7]: (D_12=B_8 | D_12=A_7 | ~r2_hidden(D_12, k2_tarski(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.95/6.03  tff(c_736, plain, (![B_183, A_184]: ('#skF_5'(k1_tarski(B_183))=B_183 | B_183=A_184 | k1_tarski(B_183)=k1_xboole_0)), inference(resolution, [status(thm)], [c_712, c_20])).
% 13.95/6.03  tff(c_754, plain, (![B_183]: (k1_tarski(B_183)=k1_xboole_0 | '#skF_5'(k1_tarski(B_183))=B_183)), inference(factorization, [status(thm), theory('equality')], [c_736])).
% 13.95/6.03  tff(c_322, plain, (![B_14]: (k1_tarski(B_14)=k1_xboole_0 | r2_hidden(B_14, k1_tarski(B_14)))), inference(superposition, [status(thm), theory('equality')], [c_293, c_40])).
% 13.95/6.03  tff(c_480, plain, (![C_132, A_133, D_134, E_135]: (~r2_hidden(C_132, A_133) | k3_mcart_1(C_132, D_134, E_135)!='#skF_5'(A_133) | k1_xboole_0=A_133)), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.95/6.03  tff(c_19675, plain, (![B_10613, D_10614, E_10615]: (k3_mcart_1(B_10613, D_10614, E_10615)!='#skF_5'(k1_tarski(B_10613)) | k1_tarski(B_10613)=k1_xboole_0)), inference(resolution, [status(thm)], [c_322, c_480])).
% 13.95/6.03  tff(c_19678, plain, (![B_183, D_10614, E_10615]: (k3_mcart_1(B_183, D_10614, E_10615)!=B_183 | k1_tarski(B_183)=k1_xboole_0 | k1_tarski(B_183)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_754, c_19675])).
% 13.95/6.03  tff(c_20184, plain, (k1_tarski('#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20144, c_19678])).
% 13.95/6.03  tff(c_38, plain, (![B_14, A_13]: (~r2_hidden(B_14, A_13) | k4_xboole_0(A_13, k1_tarski(B_14))!=A_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.95/6.03  tff(c_20267, plain, (![A_10700]: (~r2_hidden('#skF_10', A_10700) | k4_xboole_0(A_10700, k1_xboole_0)!=A_10700)), inference(superposition, [status(thm), theory('equality')], [c_20184, c_38])).
% 13.95/6.03  tff(c_20384, plain, (![B_10706]: (k4_xboole_0(k2_tarski('#skF_10', B_10706), k1_xboole_0)!=k2_tarski('#skF_10', B_10706))), inference(resolution, [status(thm)], [c_24, c_20267])).
% 13.95/6.03  tff(c_20388, plain, (![B_16]: (r2_hidden(B_16, k1_xboole_0) | r2_hidden('#skF_10', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_20384])).
% 13.95/6.03  tff(c_20392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_353, c_20388])).
% 13.95/6.03  tff(c_20393, plain, (k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10' | k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_66])).
% 13.95/6.03  tff(c_20395, plain, (k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(splitLeft, [status(thm)], [c_20393])).
% 13.95/6.03  tff(c_51233, plain, (![A_27858, B_27859, C_27860, D_27861]: (k3_mcart_1(k5_mcart_1(A_27858, B_27859, C_27860, D_27861), k6_mcart_1(A_27858, B_27859, C_27860, D_27861), k7_mcart_1(A_27858, B_27859, C_27860, D_27861))=D_27861 | ~m1_subset_1(D_27861, k3_zfmisc_1(A_27858, B_27859, C_27860)) | k1_xboole_0=C_27860 | k1_xboole_0=B_27859 | k1_xboole_0=A_27858)), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.95/6.03  tff(c_52064, plain, (k3_mcart_1(k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), '#skF_10')='#skF_10' | ~m1_subset_1('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_20395, c_51233])).
% 13.95/6.03  tff(c_52092, plain, (k3_mcart_1(k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), '#skF_10')='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_52064])).
% 13.95/6.03  tff(c_52093, plain, (k3_mcart_1(k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), '#skF_10')='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_70, c_52092])).
% 13.95/6.03  tff(c_48, plain, (![A_18, B_19, C_20]: (k4_tarski(k4_tarski(A_18, B_19), C_20)=k3_mcart_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.95/6.03  tff(c_20405, plain, (![D_10709, A_10710, B_10711]: (r2_hidden(D_10709, A_10710) | ~r2_hidden(D_10709, k4_xboole_0(A_10710, B_10711)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.95/6.03  tff(c_20558, plain, (![A_10766, B_10767]: (r2_hidden('#skF_5'(k4_xboole_0(A_10766, B_10767)), A_10766) | k4_xboole_0(A_10766, B_10767)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_20405])).
% 13.95/6.03  tff(c_20419, plain, (![D_10712, B_10713, A_10714]: (~r2_hidden(D_10712, B_10713) | ~r2_hidden(D_10712, k4_xboole_0(A_10714, B_10713)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.95/6.03  tff(c_20432, plain, (![A_10714, B_10713]: (~r2_hidden('#skF_5'(k4_xboole_0(A_10714, B_10713)), B_10713) | k4_xboole_0(A_10714, B_10713)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_20419])).
% 13.95/6.03  tff(c_20587, plain, (![A_10766]: (k4_xboole_0(A_10766, A_10766)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20558, c_20432])).
% 13.95/6.03  tff(c_20643, plain, (![B_10771, C_10772, A_10773]: (~r2_hidden(B_10771, C_10772) | k4_xboole_0(k2_tarski(A_10773, B_10771), C_10772)!=k2_tarski(A_10773, B_10771))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.95/6.03  tff(c_20647, plain, (![B_10771, A_10773]: (~r2_hidden(B_10771, k2_tarski(A_10773, B_10771)) | k2_tarski(A_10773, B_10771)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20587, c_20643])).
% 13.95/6.03  tff(c_20653, plain, (![A_10773, B_10771]: (k2_tarski(A_10773, B_10771)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20647])).
% 13.95/6.03  tff(c_20484, plain, (![D_10724, A_10725, C_10726]: (~r2_hidden(D_10724, A_10725) | k4_tarski(C_10726, D_10724)!='#skF_6'(A_10725) | k1_xboole_0=A_10725)), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.95/6.03  tff(c_20496, plain, (![C_10726, D_12, B_8]: (k4_tarski(C_10726, D_12)!='#skF_6'(k2_tarski(D_12, B_8)) | k2_tarski(D_12, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_20484])).
% 13.95/6.03  tff(c_53519, plain, (![C_29238, D_29239, B_29240]: (k4_tarski(C_29238, D_29239)!='#skF_6'(k2_tarski(D_29239, B_29240)))), inference(negUnitSimplification, [status(thm)], [c_20653, c_20496])).
% 13.95/6.03  tff(c_53798, plain, (![A_29364, B_29365, C_29366, B_29367]: (k3_mcart_1(A_29364, B_29365, C_29366)!='#skF_6'(k2_tarski(C_29366, B_29367)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_53519])).
% 13.95/6.03  tff(c_53801, plain, (![B_29367]: ('#skF_6'(k2_tarski('#skF_10', B_29367))!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_52093, c_53798])).
% 13.95/6.03  tff(c_60, plain, (![A_43]: (r2_hidden('#skF_6'(A_43), A_43) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.95/6.03  tff(c_20448, plain, (![D_10718, B_10719, A_10720]: (D_10718=B_10719 | D_10718=A_10720 | ~r2_hidden(D_10718, k2_tarski(A_10720, B_10719)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.95/6.03  tff(c_20463, plain, (![A_10720, B_10719]: ('#skF_6'(k2_tarski(A_10720, B_10719))=B_10719 | '#skF_6'(k2_tarski(A_10720, B_10719))=A_10720 | k2_tarski(A_10720, B_10719)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_20448])).
% 13.95/6.03  tff(c_54182, plain, (![A_29395, B_29396]: ('#skF_6'(k2_tarski(A_29395, B_29396))=B_29396 | '#skF_6'(k2_tarski(A_29395, B_29396))=A_29395)), inference(negUnitSimplification, [status(thm)], [c_20653, c_20463])).
% 13.95/6.03  tff(c_54199, plain, (![B_29396]: (B_29396!='#skF_10' | '#skF_6'(k2_tarski('#skF_10', B_29396))='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_54182, c_53801])).
% 13.95/6.03  tff(c_54285, plain, (![B_29396]: (B_29396!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_53801, c_54199])).
% 13.95/6.03  tff(c_54303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54285, c_52093])).
% 13.95/6.03  tff(c_54304, plain, (k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_20393])).
% 13.95/6.03  tff(c_89578, plain, (![A_49510, B_49511, C_49512, D_49513]: (k3_mcart_1(k5_mcart_1(A_49510, B_49511, C_49512, D_49513), k6_mcart_1(A_49510, B_49511, C_49512, D_49513), k7_mcart_1(A_49510, B_49511, C_49512, D_49513))=D_49513 | ~m1_subset_1(D_49513, k3_zfmisc_1(A_49510, B_49511, C_49512)) | k1_xboole_0=C_49512 | k1_xboole_0=B_49511 | k1_xboole_0=A_49510)), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.95/6.03  tff(c_90415, plain, (k3_mcart_1(k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), '#skF_10', k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_54304, c_89578])).
% 13.95/6.03  tff(c_90443, plain, (k3_mcart_1(k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), '#skF_10', k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_90415])).
% 13.95/6.03  tff(c_90444, plain, (k3_mcart_1(k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), '#skF_10', k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_70, c_90443])).
% 13.95/6.03  tff(c_54310, plain, (![D_29397, A_29398, B_29399]: (r2_hidden(D_29397, A_29398) | ~r2_hidden(D_29397, k4_xboole_0(A_29398, B_29399)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.95/6.03  tff(c_54457, plain, (![A_29444, B_29445]: (r2_hidden('#skF_5'(k4_xboole_0(A_29444, B_29445)), A_29444) | k4_xboole_0(A_29444, B_29445)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_54310])).
% 13.95/6.03  tff(c_54324, plain, (![D_29400, B_29401, A_29402]: (~r2_hidden(D_29400, B_29401) | ~r2_hidden(D_29400, k4_xboole_0(A_29402, B_29401)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.95/6.03  tff(c_54337, plain, (![A_29402, B_29401]: (~r2_hidden('#skF_5'(k4_xboole_0(A_29402, B_29401)), B_29401) | k4_xboole_0(A_29402, B_29401)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_54324])).
% 13.95/6.03  tff(c_54491, plain, (![A_29446]: (k4_xboole_0(A_29446, A_29446)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54457, c_54337])).
% 13.95/6.03  tff(c_46, plain, (![A_15, C_17, B_16]: (~r2_hidden(A_15, C_17) | k4_xboole_0(k2_tarski(A_15, B_16), C_17)!=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.95/6.03  tff(c_54500, plain, (![A_15, B_16]: (~r2_hidden(A_15, k2_tarski(A_15, B_16)) | k2_tarski(A_15, B_16)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54491, c_46])).
% 13.95/6.03  tff(c_54530, plain, (![A_15, B_16]: (k2_tarski(A_15, B_16)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_54500])).
% 13.95/6.03  tff(c_54534, plain, (![D_29447, A_29448, C_29449, E_29450]: (~r2_hidden(D_29447, A_29448) | k3_mcart_1(C_29449, D_29447, E_29450)!='#skF_5'(A_29448) | k1_xboole_0=A_29448)), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.95/6.03  tff(c_54549, plain, (![C_29449, D_12, E_29450, B_8]: (k3_mcart_1(C_29449, D_12, E_29450)!='#skF_5'(k2_tarski(D_12, B_8)) | k2_tarski(D_12, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_54534])).
% 13.95/6.03  tff(c_92085, plain, (![C_50827, D_50828, E_50829, B_50830]: (k3_mcart_1(C_50827, D_50828, E_50829)!='#skF_5'(k2_tarski(D_50828, B_50830)))), inference(negUnitSimplification, [status(thm)], [c_54530, c_54549])).
% 13.95/6.03  tff(c_92088, plain, (![B_50830]: ('#skF_5'(k2_tarski('#skF_10', B_50830))!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_90444, c_92085])).
% 13.95/6.03  tff(c_54343, plain, (![D_29405, B_29406, A_29407]: (D_29405=B_29406 | D_29405=A_29407 | ~r2_hidden(D_29405, k2_tarski(A_29407, B_29406)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.95/6.03  tff(c_54359, plain, (![A_29407, B_29406]: ('#skF_5'(k2_tarski(A_29407, B_29406))=B_29406 | '#skF_5'(k2_tarski(A_29407, B_29406))=A_29407 | k2_tarski(A_29407, B_29406)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_54343])).
% 13.95/6.03  tff(c_92499, plain, (![A_50872, B_50873]: ('#skF_5'(k2_tarski(A_50872, B_50873))=B_50873 | '#skF_5'(k2_tarski(A_50872, B_50873))=A_50872)), inference(negUnitSimplification, [status(thm)], [c_54530, c_54359])).
% 13.95/6.03  tff(c_92517, plain, (![B_50873]: (B_50873!='#skF_10' | '#skF_5'(k2_tarski('#skF_10', B_50873))='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_92499, c_92088])).
% 13.95/6.03  tff(c_92617, plain, (![B_50873]: (B_50873!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_92088, c_92517])).
% 13.95/6.03  tff(c_92640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92617, c_90444])).
% 13.95/6.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.95/6.03  
% 13.95/6.03  Inference rules
% 13.95/6.03  ----------------------
% 13.95/6.03  #Ref     : 0
% 13.95/6.03  #Sup     : 13762
% 13.95/6.03  #Fact    : 22
% 13.95/6.03  #Define  : 0
% 13.95/6.03  #Split   : 23
% 13.95/6.03  #Chain   : 0
% 13.95/6.03  #Close   : 0
% 13.95/6.03  
% 13.95/6.03  Ordering : KBO
% 13.95/6.03  
% 13.95/6.03  Simplification rules
% 13.95/6.03  ----------------------
% 13.95/6.03  #Subsume      : 3157
% 13.95/6.03  #Demod        : 4173
% 13.95/6.03  #Tautology    : 1681
% 13.95/6.03  #SimpNegUnit  : 1579
% 13.95/6.03  #BackRed      : 40
% 13.95/6.03  
% 13.95/6.03  #Partial instantiations: 25410
% 13.95/6.03  #Strategies tried      : 1
% 13.95/6.03  
% 13.95/6.03  Timing (in seconds)
% 13.95/6.03  ----------------------
% 13.95/6.03  Preprocessing        : 0.33
% 13.95/6.03  Parsing              : 0.17
% 13.95/6.03  CNF conversion       : 0.03
% 13.95/6.03  Main loop            : 4.92
% 13.95/6.03  Inferencing          : 1.66
% 13.95/6.03  Reduction            : 1.44
% 13.95/6.03  Demodulation         : 0.86
% 13.95/6.03  BG Simplification    : 0.27
% 13.95/6.03  Subsumption          : 1.12
% 13.95/6.03  Abstraction          : 0.35
% 13.95/6.03  MUC search           : 0.00
% 13.95/6.03  Cooper               : 0.00
% 13.95/6.03  Total                : 5.30
% 13.95/6.03  Index Insertion      : 0.00
% 13.95/6.03  Index Deletion       : 0.00
% 13.95/6.03  Index Matching       : 0.00
% 13.95/6.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
