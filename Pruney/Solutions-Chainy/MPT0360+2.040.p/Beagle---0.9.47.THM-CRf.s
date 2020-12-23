%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:23 EST 2020

% Result     : Theorem 15.59s
% Output     : CNFRefutation 15.59s
% Verified   : 
% Statistics : Number of formulae       :  138 (1032 expanded)
%              Number of leaves         :   32 ( 357 expanded)
%              Depth                    :   17
%              Number of atoms          :  223 (2212 expanded)
%              Number of equality atoms :   62 ( 436 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_56,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_477,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = k3_subset_1(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_486,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_477])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_tarski(A_8,k4_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_686,plain,(
    ! [A_105] :
      ( r1_xboole_0(A_105,'#skF_6')
      | ~ r1_tarski(A_105,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_10])).

tff(c_711,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_686])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( ~ r1_xboole_0(B_14,A_13)
      | ~ r1_tarski(B_14,A_13)
      | v1_xboole_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_729,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_711,c_18])).

tff(c_735,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_729])).

tff(c_123,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [A_54] : r1_tarski(A_54,A_54) ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_736,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_711,c_22])).

tff(c_26,plain,(
    ! [A_19,C_21,B_20] :
      ( r1_xboole_0(A_19,k4_xboole_0(C_21,B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_804,plain,(
    ! [A_110] :
      ( r1_xboole_0(A_110,'#skF_5')
      | ~ r1_tarski(A_110,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_26])).

tff(c_836,plain,(
    ! [A_112] :
      ( k4_xboole_0(A_112,'#skF_5') = A_112
      | ~ r1_tarski(A_112,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_804,c_22])).

tff(c_858,plain,(
    k4_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_132,c_836])).

tff(c_30,plain,(
    ! [C_26,A_22] :
      ( r2_hidden(C_26,k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_337,plain,(
    ! [B_80,A_81] :
      ( m1_subset_1(B_80,A_81)
      | ~ r2_hidden(B_80,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4338,plain,(
    ! [C_202,A_203] :
      ( m1_subset_1(C_202,k1_zfmisc_1(A_203))
      | v1_xboole_0(k1_zfmisc_1(A_203))
      | ~ r1_tarski(C_202,A_203) ) ),
    inference(resolution,[status(thm)],[c_30,c_337])).

tff(c_48,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k3_subset_1(A_29,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28224,plain,(
    ! [A_575,C_576] :
      ( k4_xboole_0(A_575,C_576) = k3_subset_1(A_575,C_576)
      | v1_xboole_0(k1_zfmisc_1(A_575))
      | ~ r1_tarski(C_576,A_575) ) ),
    inference(resolution,[status(thm)],[c_4338,c_48])).

tff(c_28266,plain,
    ( k4_xboole_0('#skF_6','#skF_5') = k3_subset_1('#skF_6','#skF_5')
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_28224])).

tff(c_28302,plain,
    ( k3_subset_1('#skF_6','#skF_5') = '#skF_6'
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_28266])).

tff(c_28488,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_28302])).

tff(c_44,plain,(
    ! [B_28,A_27] :
      ( m1_subset_1(B_28,A_27)
      | ~ v1_xboole_0(B_28)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_9431,plain,(
    ! [A_293,B_294] :
      ( k4_xboole_0(A_293,B_294) = k3_subset_1(A_293,B_294)
      | ~ v1_xboole_0(B_294)
      | ~ v1_xboole_0(k1_zfmisc_1(A_293)) ) ),
    inference(resolution,[status(thm)],[c_44,c_477])).

tff(c_9463,plain,(
    ! [A_293] :
      ( k4_xboole_0(A_293,'#skF_5') = k3_subset_1(A_293,'#skF_5')
      | ~ v1_xboole_0(k1_zfmisc_1(A_293)) ) ),
    inference(resolution,[status(thm)],[c_735,c_9431])).

tff(c_28494,plain,(
    k4_xboole_0('#skF_6','#skF_5') = k3_subset_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_28488,c_9463])).

tff(c_28504,plain,(
    k3_subset_1('#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_28494])).

tff(c_564,plain,(
    ! [A_99,B_100] :
      ( k3_subset_1(A_99,k3_subset_1(A_99,B_100)) = B_100
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_570,plain,(
    ! [A_99,B_28] :
      ( k3_subset_1(A_99,k3_subset_1(A_99,B_28)) = B_28
      | ~ v1_xboole_0(B_28)
      | ~ v1_xboole_0(k1_zfmisc_1(A_99)) ) ),
    inference(resolution,[status(thm)],[c_44,c_564])).

tff(c_34826,plain,(
    ! [B_649] :
      ( k3_subset_1('#skF_6',k3_subset_1('#skF_6',B_649)) = B_649
      | ~ v1_xboole_0(B_649) ) ),
    inference(resolution,[status(thm)],[c_28488,c_570])).

tff(c_34853,plain,
    ( k3_subset_1('#skF_6','#skF_6') = '#skF_5'
    | ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28504,c_34826])).

tff(c_34873,plain,(
    k3_subset_1('#skF_6','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_34853])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_xboole_0(A_56,C_57)
      | ~ r1_tarski(A_56,k4_xboole_0(B_58,C_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,(
    ! [C_57] : r1_xboole_0(k1_xboole_0,C_57) ),
    inference(resolution,[status(thm)],[c_14,c_134])).

tff(c_285,plain,(
    ! [B_77,A_78] :
      ( ~ r1_xboole_0(B_77,A_78)
      | ~ r1_tarski(B_77,A_78)
      | v1_xboole_0(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_294,plain,(
    ! [C_57] :
      ( ~ r1_tarski(k1_xboole_0,C_57)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_143,c_285])).

tff(c_308,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_294])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28264,plain,(
    ! [A_11] :
      ( k4_xboole_0(A_11,k1_xboole_0) = k3_subset_1(A_11,k1_xboole_0)
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_14,c_28224])).

tff(c_29748,plain,(
    ! [A_583] :
      ( k3_subset_1(A_583,k1_xboole_0) = A_583
      | v1_xboole_0(k1_zfmisc_1(A_583)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_28264])).

tff(c_9455,plain,(
    ! [A_293] :
      ( k4_xboole_0(A_293,k1_xboole_0) = k3_subset_1(A_293,k1_xboole_0)
      | ~ v1_xboole_0(k1_zfmisc_1(A_293)) ) ),
    inference(resolution,[status(thm)],[c_308,c_9431])).

tff(c_9468,plain,(
    ! [A_293] :
      ( k3_subset_1(A_293,k1_xboole_0) = A_293
      | ~ v1_xboole_0(k1_zfmisc_1(A_293)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_9455])).

tff(c_29767,plain,(
    ! [A_583] : k3_subset_1(A_583,k1_xboole_0) = A_583 ),
    inference(resolution,[status(thm)],[c_29748,c_9468])).

tff(c_34850,plain,
    ( k3_subset_1('#skF_6','#skF_6') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_29767,c_34826])).

tff(c_34871,plain,(
    k3_subset_1('#skF_6','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_34850])).

tff(c_34928,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34873,c_34871])).

tff(c_34930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_34928])).

tff(c_34932,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_28302])).

tff(c_196,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(A_66,B_67)
      | ~ r1_tarski(A_66,k4_xboole_0(B_67,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_211,plain,(
    ! [B_67,C_68] : r1_tarski(k4_xboole_0(B_67,C_68),B_67) ),
    inference(resolution,[status(thm)],[c_132,c_196])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_375,plain,(
    ! [C_87,B_88,A_89] :
      ( r2_hidden(C_87,B_88)
      | ~ r2_hidden(C_87,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7583,plain,(
    ! [A_258,B_259,B_260] :
      ( r2_hidden('#skF_1'(A_258,B_259),B_260)
      | ~ r1_tarski(A_258,B_260)
      | r1_tarski(A_258,B_259) ) ),
    inference(resolution,[status(thm)],[c_6,c_375])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39564,plain,(
    ! [A_690,B_691,B_692,B_693] :
      ( r2_hidden('#skF_1'(A_690,B_691),B_692)
      | ~ r1_tarski(B_693,B_692)
      | ~ r1_tarski(A_690,B_693)
      | r1_tarski(A_690,B_691) ) ),
    inference(resolution,[status(thm)],[c_7583,c_2])).

tff(c_39754,plain,(
    ! [A_697,B_698] :
      ( r2_hidden('#skF_1'(A_697,B_698),'#skF_6')
      | ~ r1_tarski(A_697,'#skF_5')
      | r1_tarski(A_697,B_698) ) ),
    inference(resolution,[status(thm)],[c_56,c_39564])).

tff(c_39768,plain,(
    ! [A_699] :
      ( ~ r1_tarski(A_699,'#skF_5')
      | r1_tarski(A_699,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_39754,c_4])).

tff(c_39829,plain,(
    ! [C_68] : r1_tarski(k4_xboole_0('#skF_5',C_68),'#skF_6') ),
    inference(resolution,[status(thm)],[c_211,c_39768])).

tff(c_35384,plain,(
    ! [A_653] :
      ( k3_subset_1(A_653,k1_xboole_0) = A_653
      | v1_xboole_0(k1_zfmisc_1(A_653)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_28264])).

tff(c_35437,plain,(
    ! [A_657] : k3_subset_1(A_657,k1_xboole_0) = A_657 ),
    inference(resolution,[status(thm)],[c_35384,c_9468])).

tff(c_50,plain,(
    ! [A_31,B_32] :
      ( k3_subset_1(A_31,k3_subset_1(A_31,B_32)) = B_32
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4347,plain,(
    ! [A_203,C_202] :
      ( k3_subset_1(A_203,k3_subset_1(A_203,C_202)) = C_202
      | v1_xboole_0(k1_zfmisc_1(A_203))
      | ~ r1_tarski(C_202,A_203) ) ),
    inference(resolution,[status(thm)],[c_4338,c_50])).

tff(c_35447,plain,(
    ! [A_657] :
      ( k3_subset_1(A_657,A_657) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_657))
      | ~ r1_tarski(k1_xboole_0,A_657) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35437,c_4347])).

tff(c_35486,plain,(
    ! [A_658] :
      ( k3_subset_1(A_658,A_658) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_658)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_35447])).

tff(c_35522,plain,(
    k3_subset_1('#skF_6','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35486,c_34932])).

tff(c_214,plain,(
    ! [B_69,C_70] : r1_tarski(k4_xboole_0(B_69,C_70),B_69) ),
    inference(resolution,[status(thm)],[c_132,c_196])).

tff(c_235,plain,(
    ! [B_9,C_10,C_70] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_9,C_10),C_70),C_10) ),
    inference(resolution,[status(thm)],[c_214,c_10])).

tff(c_778,plain,(
    ! [C_108] : r1_xboole_0(k4_xboole_0('#skF_5',C_108),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_235])).

tff(c_792,plain,(
    ! [C_108] : k4_xboole_0(k4_xboole_0('#skF_5',C_108),'#skF_6') = k4_xboole_0('#skF_5',C_108) ),
    inference(resolution,[status(thm)],[c_778,c_22])).

tff(c_359,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_xboole_0(A_84,k4_xboole_0(C_85,B_86))
      | ~ r1_tarski(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1698,plain,(
    ! [A_149,C_150,B_151] :
      ( k4_xboole_0(A_149,k4_xboole_0(C_150,B_151)) = A_149
      | ~ r1_tarski(A_149,B_151) ) ),
    inference(resolution,[status(thm)],[c_359,c_22])).

tff(c_3318,plain,(
    ! [A_188,C_189] :
      ( k4_xboole_0(A_188,k4_xboole_0('#skF_5',C_189)) = A_188
      | ~ r1_tarski(A_188,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_1698])).

tff(c_857,plain,(
    ! [C_68] : k4_xboole_0(k4_xboole_0('#skF_6',C_68),'#skF_5') = k4_xboole_0('#skF_6',C_68) ),
    inference(resolution,[status(thm)],[c_211,c_836])).

tff(c_3446,plain,(
    ! [C_189] :
      ( k4_xboole_0('#skF_6',k4_xboole_0('#skF_5',C_189)) = k4_xboole_0('#skF_6','#skF_5')
      | ~ r1_tarski('#skF_6','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3318,c_857])).

tff(c_3641,plain,(
    ! [C_189] : k4_xboole_0('#skF_6',k4_xboole_0('#skF_5',C_189)) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_858,c_3446])).

tff(c_39834,plain,(
    ! [C_700] : r1_tarski(k4_xboole_0('#skF_5',C_700),'#skF_6') ),
    inference(resolution,[status(thm)],[c_211,c_39768])).

tff(c_4348,plain,(
    ! [A_203,C_202] :
      ( k4_xboole_0(A_203,C_202) = k3_subset_1(A_203,C_202)
      | v1_xboole_0(k1_zfmisc_1(A_203))
      | ~ r1_tarski(C_202,A_203) ) ),
    inference(resolution,[status(thm)],[c_4338,c_48])).

tff(c_39843,plain,(
    ! [C_700] :
      ( k4_xboole_0('#skF_6',k4_xboole_0('#skF_5',C_700)) = k3_subset_1('#skF_6',k4_xboole_0('#skF_5',C_700))
      | v1_xboole_0(k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_39834,c_4348])).

tff(c_39938,plain,(
    ! [C_700] :
      ( k3_subset_1('#skF_6',k4_xboole_0('#skF_5',C_700)) = '#skF_6'
      | v1_xboole_0(k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3641,c_39843])).

tff(c_40131,plain,(
    ! [C_702] : k3_subset_1('#skF_6',k4_xboole_0('#skF_5',C_702)) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_34932,c_39938])).

tff(c_40136,plain,(
    ! [C_702] :
      ( k4_xboole_0('#skF_5',C_702) = k3_subset_1('#skF_6','#skF_6')
      | v1_xboole_0(k1_zfmisc_1('#skF_6'))
      | ~ r1_tarski(k4_xboole_0('#skF_5',C_702),'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40131,c_4347])).

tff(c_40205,plain,(
    ! [C_702] :
      ( k4_xboole_0('#skF_5',C_702) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39829,c_35522,c_40136])).

tff(c_40206,plain,(
    ! [C_702] : k4_xboole_0('#skF_5',C_702) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34932,c_40205])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(A_8,B_9)
      | ~ r1_tarski(A_8,k4_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_232,plain,(
    ! [B_9,C_10,C_70] : r1_tarski(k4_xboole_0(k4_xboole_0(B_9,C_10),C_70),B_9) ),
    inference(resolution,[status(thm)],[c_214,c_12])).

tff(c_1953,plain,(
    ! [A_154] :
      ( k4_xboole_0(A_154,k3_subset_1('#skF_4','#skF_6')) = A_154
      | ~ r1_tarski(A_154,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_1698])).

tff(c_2022,plain,
    ( k4_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_6')) = k4_xboole_0('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1953,c_792])).

tff(c_2149,plain,(
    k4_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_736,c_2022])).

tff(c_2495,plain,(
    ! [A_162] :
      ( r1_xboole_0(A_162,k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_162,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2149,c_10])).

tff(c_2503,plain,(
    ! [A_162] :
      ( k4_xboole_0(A_162,k3_subset_1('#skF_4','#skF_6')) = A_162
      | ~ r1_tarski(A_162,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2495,c_22])).

tff(c_14047,plain,(
    ! [A_379,C_380,B_381,A_382] :
      ( r1_xboole_0(A_379,k4_xboole_0(C_380,B_381))
      | ~ r1_tarski(A_379,A_382)
      | ~ r1_tarski(A_382,B_381) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1698,c_10])).

tff(c_14486,plain,(
    ! [C_391,B_392] :
      ( r1_xboole_0('#skF_5',k4_xboole_0(C_391,B_392))
      | ~ r1_tarski(k3_subset_1('#skF_4','#skF_6'),B_392) ) ),
    inference(resolution,[status(thm)],[c_54,c_14047])).

tff(c_14522,plain,(
    ! [A_162] :
      ( r1_xboole_0('#skF_5',A_162)
      | ~ r1_tarski(k3_subset_1('#skF_4','#skF_6'),k3_subset_1('#skF_4','#skF_6'))
      | ~ r1_tarski(A_162,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2503,c_14486])).

tff(c_14620,plain,(
    ! [A_393] :
      ( r1_xboole_0('#skF_5',A_393)
      | ~ r1_tarski(A_393,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_14522])).

tff(c_14630,plain,(
    ! [A_394] :
      ( k4_xboole_0('#skF_5',A_394) = '#skF_5'
      | ~ r1_tarski(A_394,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14620,c_22])).

tff(c_14671,plain,(
    ! [C_10,C_70] : k4_xboole_0('#skF_5',k4_xboole_0(k4_xboole_0('#skF_5',C_10),C_70)) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_232,c_14630])).

tff(c_40260,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40206,c_40206,c_14671])).

tff(c_40335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_40260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:54:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.59/6.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.59/6.86  
% 15.59/6.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.59/6.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 15.59/6.87  
% 15.59/6.87  %Foreground sorts:
% 15.59/6.87  
% 15.59/6.87  
% 15.59/6.87  %Background operators:
% 15.59/6.87  
% 15.59/6.87  
% 15.59/6.87  %Foreground operators:
% 15.59/6.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.59/6.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.59/6.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.59/6.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.59/6.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.59/6.87  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.59/6.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.59/6.87  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 15.59/6.87  tff('#skF_5', type, '#skF_5': $i).
% 15.59/6.87  tff('#skF_6', type, '#skF_6': $i).
% 15.59/6.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.59/6.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.59/6.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.59/6.87  tff('#skF_4', type, '#skF_4': $i).
% 15.59/6.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.59/6.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.59/6.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.59/6.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.59/6.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.59/6.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.59/6.87  
% 15.59/6.89  tff(f_99, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 15.59/6.89  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 15.59/6.89  tff(f_40, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 15.59/6.89  tff(f_52, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 15.59/6.89  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.59/6.89  tff(f_58, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 15.59/6.89  tff(f_62, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 15.59/6.89  tff(f_69, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 15.59/6.89  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 15.59/6.89  tff(f_90, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 15.59/6.89  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 15.59/6.89  tff(f_44, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 15.59/6.89  tff(c_52, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.59/6.89  tff(c_56, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.59/6.89  tff(c_54, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.59/6.89  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.59/6.89  tff(c_477, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)=k3_subset_1(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.59/6.89  tff(c_486, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_477])).
% 15.59/6.89  tff(c_10, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_tarski(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.59/6.89  tff(c_686, plain, (![A_105]: (r1_xboole_0(A_105, '#skF_6') | ~r1_tarski(A_105, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_486, c_10])).
% 15.59/6.89  tff(c_711, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_686])).
% 15.59/6.89  tff(c_18, plain, (![B_14, A_13]: (~r1_xboole_0(B_14, A_13) | ~r1_tarski(B_14, A_13) | v1_xboole_0(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.59/6.89  tff(c_729, plain, (~r1_tarski('#skF_5', '#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_711, c_18])).
% 15.59/6.89  tff(c_735, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_729])).
% 15.59/6.89  tff(c_123, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.59/6.89  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.59/6.89  tff(c_132, plain, (![A_54]: (r1_tarski(A_54, A_54))), inference(resolution, [status(thm)], [c_123, c_4])).
% 15.59/6.89  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.59/6.89  tff(c_736, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_711, c_22])).
% 15.59/6.89  tff(c_26, plain, (![A_19, C_21, B_20]: (r1_xboole_0(A_19, k4_xboole_0(C_21, B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.59/6.89  tff(c_804, plain, (![A_110]: (r1_xboole_0(A_110, '#skF_5') | ~r1_tarski(A_110, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_736, c_26])).
% 15.59/6.89  tff(c_836, plain, (![A_112]: (k4_xboole_0(A_112, '#skF_5')=A_112 | ~r1_tarski(A_112, '#skF_6'))), inference(resolution, [status(thm)], [c_804, c_22])).
% 15.59/6.89  tff(c_858, plain, (k4_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_132, c_836])).
% 15.59/6.89  tff(c_30, plain, (![C_26, A_22]: (r2_hidden(C_26, k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.59/6.89  tff(c_337, plain, (![B_80, A_81]: (m1_subset_1(B_80, A_81) | ~r2_hidden(B_80, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_82])).
% 15.59/6.89  tff(c_4338, plain, (![C_202, A_203]: (m1_subset_1(C_202, k1_zfmisc_1(A_203)) | v1_xboole_0(k1_zfmisc_1(A_203)) | ~r1_tarski(C_202, A_203))), inference(resolution, [status(thm)], [c_30, c_337])).
% 15.59/6.89  tff(c_48, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k3_subset_1(A_29, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.59/6.89  tff(c_28224, plain, (![A_575, C_576]: (k4_xboole_0(A_575, C_576)=k3_subset_1(A_575, C_576) | v1_xboole_0(k1_zfmisc_1(A_575)) | ~r1_tarski(C_576, A_575))), inference(resolution, [status(thm)], [c_4338, c_48])).
% 15.59/6.89  tff(c_28266, plain, (k4_xboole_0('#skF_6', '#skF_5')=k3_subset_1('#skF_6', '#skF_5') | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_56, c_28224])).
% 15.59/6.89  tff(c_28302, plain, (k3_subset_1('#skF_6', '#skF_5')='#skF_6' | v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_858, c_28266])).
% 15.59/6.89  tff(c_28488, plain, (v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_28302])).
% 15.59/6.89  tff(c_44, plain, (![B_28, A_27]: (m1_subset_1(B_28, A_27) | ~v1_xboole_0(B_28) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 15.59/6.89  tff(c_9431, plain, (![A_293, B_294]: (k4_xboole_0(A_293, B_294)=k3_subset_1(A_293, B_294) | ~v1_xboole_0(B_294) | ~v1_xboole_0(k1_zfmisc_1(A_293)))), inference(resolution, [status(thm)], [c_44, c_477])).
% 15.59/6.89  tff(c_9463, plain, (![A_293]: (k4_xboole_0(A_293, '#skF_5')=k3_subset_1(A_293, '#skF_5') | ~v1_xboole_0(k1_zfmisc_1(A_293)))), inference(resolution, [status(thm)], [c_735, c_9431])).
% 15.59/6.89  tff(c_28494, plain, (k4_xboole_0('#skF_6', '#skF_5')=k3_subset_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_28488, c_9463])).
% 15.59/6.89  tff(c_28504, plain, (k3_subset_1('#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_858, c_28494])).
% 15.59/6.89  tff(c_564, plain, (![A_99, B_100]: (k3_subset_1(A_99, k3_subset_1(A_99, B_100))=B_100 | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.59/6.89  tff(c_570, plain, (![A_99, B_28]: (k3_subset_1(A_99, k3_subset_1(A_99, B_28))=B_28 | ~v1_xboole_0(B_28) | ~v1_xboole_0(k1_zfmisc_1(A_99)))), inference(resolution, [status(thm)], [c_44, c_564])).
% 15.59/6.89  tff(c_34826, plain, (![B_649]: (k3_subset_1('#skF_6', k3_subset_1('#skF_6', B_649))=B_649 | ~v1_xboole_0(B_649))), inference(resolution, [status(thm)], [c_28488, c_570])).
% 15.59/6.89  tff(c_34853, plain, (k3_subset_1('#skF_6', '#skF_6')='#skF_5' | ~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28504, c_34826])).
% 15.59/6.89  tff(c_34873, plain, (k3_subset_1('#skF_6', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_735, c_34853])).
% 15.59/6.89  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.59/6.89  tff(c_134, plain, (![A_56, C_57, B_58]: (r1_xboole_0(A_56, C_57) | ~r1_tarski(A_56, k4_xboole_0(B_58, C_57)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.59/6.89  tff(c_143, plain, (![C_57]: (r1_xboole_0(k1_xboole_0, C_57))), inference(resolution, [status(thm)], [c_14, c_134])).
% 15.59/6.89  tff(c_285, plain, (![B_77, A_78]: (~r1_xboole_0(B_77, A_78) | ~r1_tarski(B_77, A_78) | v1_xboole_0(B_77))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.59/6.89  tff(c_294, plain, (![C_57]: (~r1_tarski(k1_xboole_0, C_57) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_143, c_285])).
% 15.59/6.89  tff(c_308, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_294])).
% 15.59/6.89  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.59/6.89  tff(c_28264, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=k3_subset_1(A_11, k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_14, c_28224])).
% 15.59/6.89  tff(c_29748, plain, (![A_583]: (k3_subset_1(A_583, k1_xboole_0)=A_583 | v1_xboole_0(k1_zfmisc_1(A_583)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_28264])).
% 15.59/6.89  tff(c_9455, plain, (![A_293]: (k4_xboole_0(A_293, k1_xboole_0)=k3_subset_1(A_293, k1_xboole_0) | ~v1_xboole_0(k1_zfmisc_1(A_293)))), inference(resolution, [status(thm)], [c_308, c_9431])).
% 15.59/6.89  tff(c_9468, plain, (![A_293]: (k3_subset_1(A_293, k1_xboole_0)=A_293 | ~v1_xboole_0(k1_zfmisc_1(A_293)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_9455])).
% 15.59/6.89  tff(c_29767, plain, (![A_583]: (k3_subset_1(A_583, k1_xboole_0)=A_583)), inference(resolution, [status(thm)], [c_29748, c_9468])).
% 15.59/6.89  tff(c_34850, plain, (k3_subset_1('#skF_6', '#skF_6')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_29767, c_34826])).
% 15.59/6.89  tff(c_34871, plain, (k3_subset_1('#skF_6', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_308, c_34850])).
% 15.59/6.89  tff(c_34928, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_34873, c_34871])).
% 15.59/6.89  tff(c_34930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_34928])).
% 15.59/6.89  tff(c_34932, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_28302])).
% 15.59/6.89  tff(c_196, plain, (![A_66, B_67, C_68]: (r1_tarski(A_66, B_67) | ~r1_tarski(A_66, k4_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.59/6.89  tff(c_211, plain, (![B_67, C_68]: (r1_tarski(k4_xboole_0(B_67, C_68), B_67))), inference(resolution, [status(thm)], [c_132, c_196])).
% 15.59/6.89  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.59/6.89  tff(c_375, plain, (![C_87, B_88, A_89]: (r2_hidden(C_87, B_88) | ~r2_hidden(C_87, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.59/6.89  tff(c_7583, plain, (![A_258, B_259, B_260]: (r2_hidden('#skF_1'(A_258, B_259), B_260) | ~r1_tarski(A_258, B_260) | r1_tarski(A_258, B_259))), inference(resolution, [status(thm)], [c_6, c_375])).
% 15.59/6.89  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.59/6.89  tff(c_39564, plain, (![A_690, B_691, B_692, B_693]: (r2_hidden('#skF_1'(A_690, B_691), B_692) | ~r1_tarski(B_693, B_692) | ~r1_tarski(A_690, B_693) | r1_tarski(A_690, B_691))), inference(resolution, [status(thm)], [c_7583, c_2])).
% 15.59/6.89  tff(c_39754, plain, (![A_697, B_698]: (r2_hidden('#skF_1'(A_697, B_698), '#skF_6') | ~r1_tarski(A_697, '#skF_5') | r1_tarski(A_697, B_698))), inference(resolution, [status(thm)], [c_56, c_39564])).
% 15.59/6.89  tff(c_39768, plain, (![A_699]: (~r1_tarski(A_699, '#skF_5') | r1_tarski(A_699, '#skF_6'))), inference(resolution, [status(thm)], [c_39754, c_4])).
% 15.59/6.89  tff(c_39829, plain, (![C_68]: (r1_tarski(k4_xboole_0('#skF_5', C_68), '#skF_6'))), inference(resolution, [status(thm)], [c_211, c_39768])).
% 15.59/6.89  tff(c_35384, plain, (![A_653]: (k3_subset_1(A_653, k1_xboole_0)=A_653 | v1_xboole_0(k1_zfmisc_1(A_653)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_28264])).
% 15.59/6.89  tff(c_35437, plain, (![A_657]: (k3_subset_1(A_657, k1_xboole_0)=A_657)), inference(resolution, [status(thm)], [c_35384, c_9468])).
% 15.59/6.89  tff(c_50, plain, (![A_31, B_32]: (k3_subset_1(A_31, k3_subset_1(A_31, B_32))=B_32 | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.59/6.89  tff(c_4347, plain, (![A_203, C_202]: (k3_subset_1(A_203, k3_subset_1(A_203, C_202))=C_202 | v1_xboole_0(k1_zfmisc_1(A_203)) | ~r1_tarski(C_202, A_203))), inference(resolution, [status(thm)], [c_4338, c_50])).
% 15.59/6.89  tff(c_35447, plain, (![A_657]: (k3_subset_1(A_657, A_657)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_657)) | ~r1_tarski(k1_xboole_0, A_657))), inference(superposition, [status(thm), theory('equality')], [c_35437, c_4347])).
% 15.59/6.89  tff(c_35486, plain, (![A_658]: (k3_subset_1(A_658, A_658)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_658)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_35447])).
% 15.59/6.89  tff(c_35522, plain, (k3_subset_1('#skF_6', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_35486, c_34932])).
% 15.59/6.89  tff(c_214, plain, (![B_69, C_70]: (r1_tarski(k4_xboole_0(B_69, C_70), B_69))), inference(resolution, [status(thm)], [c_132, c_196])).
% 15.59/6.89  tff(c_235, plain, (![B_9, C_10, C_70]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_9, C_10), C_70), C_10))), inference(resolution, [status(thm)], [c_214, c_10])).
% 15.59/6.89  tff(c_778, plain, (![C_108]: (r1_xboole_0(k4_xboole_0('#skF_5', C_108), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_736, c_235])).
% 15.59/6.89  tff(c_792, plain, (![C_108]: (k4_xboole_0(k4_xboole_0('#skF_5', C_108), '#skF_6')=k4_xboole_0('#skF_5', C_108))), inference(resolution, [status(thm)], [c_778, c_22])).
% 15.59/6.89  tff(c_359, plain, (![A_84, C_85, B_86]: (r1_xboole_0(A_84, k4_xboole_0(C_85, B_86)) | ~r1_tarski(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.59/6.89  tff(c_1698, plain, (![A_149, C_150, B_151]: (k4_xboole_0(A_149, k4_xboole_0(C_150, B_151))=A_149 | ~r1_tarski(A_149, B_151))), inference(resolution, [status(thm)], [c_359, c_22])).
% 15.59/6.89  tff(c_3318, plain, (![A_188, C_189]: (k4_xboole_0(A_188, k4_xboole_0('#skF_5', C_189))=A_188 | ~r1_tarski(A_188, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_792, c_1698])).
% 15.59/6.89  tff(c_857, plain, (![C_68]: (k4_xboole_0(k4_xboole_0('#skF_6', C_68), '#skF_5')=k4_xboole_0('#skF_6', C_68))), inference(resolution, [status(thm)], [c_211, c_836])).
% 15.59/6.89  tff(c_3446, plain, (![C_189]: (k4_xboole_0('#skF_6', k4_xboole_0('#skF_5', C_189))=k4_xboole_0('#skF_6', '#skF_5') | ~r1_tarski('#skF_6', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3318, c_857])).
% 15.59/6.89  tff(c_3641, plain, (![C_189]: (k4_xboole_0('#skF_6', k4_xboole_0('#skF_5', C_189))='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_858, c_3446])).
% 15.59/6.89  tff(c_39834, plain, (![C_700]: (r1_tarski(k4_xboole_0('#skF_5', C_700), '#skF_6'))), inference(resolution, [status(thm)], [c_211, c_39768])).
% 15.59/6.89  tff(c_4348, plain, (![A_203, C_202]: (k4_xboole_0(A_203, C_202)=k3_subset_1(A_203, C_202) | v1_xboole_0(k1_zfmisc_1(A_203)) | ~r1_tarski(C_202, A_203))), inference(resolution, [status(thm)], [c_4338, c_48])).
% 15.59/6.89  tff(c_39843, plain, (![C_700]: (k4_xboole_0('#skF_6', k4_xboole_0('#skF_5', C_700))=k3_subset_1('#skF_6', k4_xboole_0('#skF_5', C_700)) | v1_xboole_0(k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_39834, c_4348])).
% 15.59/6.89  tff(c_39938, plain, (![C_700]: (k3_subset_1('#skF_6', k4_xboole_0('#skF_5', C_700))='#skF_6' | v1_xboole_0(k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3641, c_39843])).
% 15.59/6.89  tff(c_40131, plain, (![C_702]: (k3_subset_1('#skF_6', k4_xboole_0('#skF_5', C_702))='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_34932, c_39938])).
% 15.59/6.89  tff(c_40136, plain, (![C_702]: (k4_xboole_0('#skF_5', C_702)=k3_subset_1('#skF_6', '#skF_6') | v1_xboole_0(k1_zfmisc_1('#skF_6')) | ~r1_tarski(k4_xboole_0('#skF_5', C_702), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_40131, c_4347])).
% 15.59/6.89  tff(c_40205, plain, (![C_702]: (k4_xboole_0('#skF_5', C_702)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_39829, c_35522, c_40136])).
% 15.59/6.89  tff(c_40206, plain, (![C_702]: (k4_xboole_0('#skF_5', C_702)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_34932, c_40205])).
% 15.59/6.89  tff(c_12, plain, (![A_8, B_9, C_10]: (r1_tarski(A_8, B_9) | ~r1_tarski(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.59/6.89  tff(c_232, plain, (![B_9, C_10, C_70]: (r1_tarski(k4_xboole_0(k4_xboole_0(B_9, C_10), C_70), B_9))), inference(resolution, [status(thm)], [c_214, c_12])).
% 15.59/6.89  tff(c_1953, plain, (![A_154]: (k4_xboole_0(A_154, k3_subset_1('#skF_4', '#skF_6'))=A_154 | ~r1_tarski(A_154, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_486, c_1698])).
% 15.59/6.89  tff(c_2022, plain, (k4_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_6'))=k4_xboole_0('#skF_5', '#skF_6') | ~r1_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1953, c_792])).
% 15.59/6.89  tff(c_2149, plain, (k4_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_736, c_2022])).
% 15.59/6.89  tff(c_2495, plain, (![A_162]: (r1_xboole_0(A_162, k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_162, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2149, c_10])).
% 15.59/6.89  tff(c_2503, plain, (![A_162]: (k4_xboole_0(A_162, k3_subset_1('#skF_4', '#skF_6'))=A_162 | ~r1_tarski(A_162, '#skF_5'))), inference(resolution, [status(thm)], [c_2495, c_22])).
% 15.59/6.89  tff(c_14047, plain, (![A_379, C_380, B_381, A_382]: (r1_xboole_0(A_379, k4_xboole_0(C_380, B_381)) | ~r1_tarski(A_379, A_382) | ~r1_tarski(A_382, B_381))), inference(superposition, [status(thm), theory('equality')], [c_1698, c_10])).
% 15.59/6.89  tff(c_14486, plain, (![C_391, B_392]: (r1_xboole_0('#skF_5', k4_xboole_0(C_391, B_392)) | ~r1_tarski(k3_subset_1('#skF_4', '#skF_6'), B_392))), inference(resolution, [status(thm)], [c_54, c_14047])).
% 15.59/6.89  tff(c_14522, plain, (![A_162]: (r1_xboole_0('#skF_5', A_162) | ~r1_tarski(k3_subset_1('#skF_4', '#skF_6'), k3_subset_1('#skF_4', '#skF_6')) | ~r1_tarski(A_162, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2503, c_14486])).
% 15.59/6.89  tff(c_14620, plain, (![A_393]: (r1_xboole_0('#skF_5', A_393) | ~r1_tarski(A_393, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_14522])).
% 15.59/6.89  tff(c_14630, plain, (![A_394]: (k4_xboole_0('#skF_5', A_394)='#skF_5' | ~r1_tarski(A_394, '#skF_5'))), inference(resolution, [status(thm)], [c_14620, c_22])).
% 15.59/6.89  tff(c_14671, plain, (![C_10, C_70]: (k4_xboole_0('#skF_5', k4_xboole_0(k4_xboole_0('#skF_5', C_10), C_70))='#skF_5')), inference(resolution, [status(thm)], [c_232, c_14630])).
% 15.59/6.89  tff(c_40260, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40206, c_40206, c_14671])).
% 15.59/6.89  tff(c_40335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_40260])).
% 15.59/6.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.59/6.89  
% 15.59/6.89  Inference rules
% 15.59/6.89  ----------------------
% 15.59/6.89  #Ref     : 0
% 15.59/6.89  #Sup     : 9888
% 15.59/6.89  #Fact    : 0
% 15.59/6.89  #Define  : 0
% 15.59/6.89  #Split   : 22
% 15.59/6.89  #Chain   : 0
% 15.59/6.89  #Close   : 0
% 15.59/6.89  
% 15.59/6.89  Ordering : KBO
% 15.59/6.89  
% 15.59/6.89  Simplification rules
% 15.59/6.89  ----------------------
% 15.59/6.89  #Subsume      : 2397
% 15.59/6.89  #Demod        : 7054
% 15.59/6.89  #Tautology    : 4948
% 15.59/6.89  #SimpNegUnit  : 68
% 15.59/6.89  #BackRed      : 98
% 15.59/6.89  
% 15.59/6.89  #Partial instantiations: 0
% 15.59/6.89  #Strategies tried      : 1
% 15.59/6.89  
% 15.59/6.89  Timing (in seconds)
% 15.59/6.89  ----------------------
% 15.59/6.89  Preprocessing        : 0.39
% 15.59/6.89  Parsing              : 0.19
% 15.59/6.89  CNF conversion       : 0.03
% 15.59/6.89  Main loop            : 5.58
% 15.59/6.89  Inferencing          : 1.00
% 15.59/6.89  Reduction            : 2.67
% 15.59/6.89  Demodulation         : 2.19
% 15.59/6.89  BG Simplification    : 0.10
% 15.59/6.89  Subsumption          : 1.52
% 15.59/6.89  Abstraction          : 0.15
% 15.59/6.89  MUC search           : 0.00
% 15.59/6.89  Cooper               : 0.00
% 15.59/6.89  Total                : 6.02
% 15.59/6.89  Index Insertion      : 0.00
% 15.59/6.89  Index Deletion       : 0.00
% 15.59/6.89  Index Matching       : 0.00
% 15.59/6.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
