%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:27 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.40s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 351 expanded)
%              Number of leaves         :   39 ( 134 expanded)
%              Depth                    :   15
%              Number of atoms          :  115 ( 489 expanded)
%              Number of equality atoms :   61 ( 341 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_58,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_60,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_68,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3743,plain,(
    ! [A_3824,B_3825,C_3826] : k5_xboole_0(k5_xboole_0(A_3824,B_3825),C_3826) = k5_xboole_0(A_3824,k5_xboole_0(B_3825,C_3826)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3905,plain,(
    ! [A_3829,B_3830] : k5_xboole_0(A_3829,k5_xboole_0(B_3830,k5_xboole_0(A_3829,B_3830))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3743,c_28])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3539,plain,(
    ! [A_3811,B_3812] : k5_xboole_0(k5_xboole_0(A_3811,B_3812),k2_xboole_0(A_3811,B_3812)) = k3_xboole_0(A_3811,B_3812) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3560,plain,(
    ! [A_6] : k5_xboole_0(k5_xboole_0(A_6,A_6),A_6) = k3_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3539])).

tff(c_3566,plain,(
    ! [A_6] : k5_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10,c_3560])).

tff(c_3820,plain,(
    ! [A_22,C_3826] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_3826)) = k5_xboole_0(k1_xboole_0,C_3826) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3743])).

tff(c_3833,plain,(
    ! [A_22,C_3826] : k5_xboole_0(A_22,k5_xboole_0(A_22,C_3826)) = C_3826 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3566,c_3820])).

tff(c_3913,plain,(
    ! [B_3830,A_3829] : k5_xboole_0(B_3830,k5_xboole_0(A_3829,B_3830)) = k5_xboole_0(A_3829,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3905,c_3833])).

tff(c_3990,plain,(
    ! [B_3830,A_3829] : k5_xboole_0(B_3830,k5_xboole_0(A_3829,B_3830)) = A_3829 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3913])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_60,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k1_tarski(A_58),B_59)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_136,plain,(
    ! [A_71,B_72] : r1_tarski(A_71,k2_xboole_0(A_71,B_72)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_136])).

tff(c_237,plain,(
    ! [B_92,A_93] :
      ( B_92 = A_93
      | ~ r1_tarski(B_92,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_249,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_139,c_237])).

tff(c_256,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_260,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_256])).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_270,plain,(
    ! [C_97,B_98,A_99] :
      ( r2_hidden(C_97,B_98)
      | ~ r2_hidden(C_97,A_99)
      | ~ r1_tarski(A_99,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_293,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_2'(A_102),B_103)
      | ~ r1_tarski(A_102,B_103)
      | k1_xboole_0 = A_102 ) ),
    inference(resolution,[status(thm)],[c_12,c_270])).

tff(c_32,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3152,plain,(
    ! [A_3679,A_3680] :
      ( A_3679 = '#skF_2'(A_3680)
      | ~ r1_tarski(A_3680,k1_tarski(A_3679))
      | k1_xboole_0 = A_3680 ) ),
    inference(resolution,[status(thm)],[c_293,c_32])).

tff(c_3167,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_139,c_3152])).

tff(c_3180,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3167])).

tff(c_3189,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3180,c_12])).

tff(c_3194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_260,c_3189])).

tff(c_3195,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_3198,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3195,c_70])).

tff(c_3554,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6','#skF_7'),'#skF_6') = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3198,c_3539])).

tff(c_3756,plain,(
    k5_xboole_0('#skF_6',k5_xboole_0('#skF_7','#skF_6')) = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3743,c_3554])).

tff(c_4092,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3990,c_3756])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(k3_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_251,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,k3_xboole_0(A_14,B_15)) ) ),
    inference(resolution,[status(thm)],[c_20,c_237])).

tff(c_4097,plain,
    ( k3_xboole_0('#skF_6','#skF_7') = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4092,c_251])).

tff(c_4106,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4092,c_4097])).

tff(c_4107,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4106])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3258,plain,(
    ! [C_3784] :
      ( C_3784 = '#skF_5'
      | ~ r2_hidden(C_3784,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3195,c_32])).

tff(c_3272,plain,(
    ! [B_2] :
      ( '#skF_1'('#skF_6',B_2) = '#skF_5'
      | r1_tarski('#skF_6',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_3258])).

tff(c_4113,plain,(
    '#skF_1'('#skF_6','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3272,c_4107])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4125,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4113,c_4])).

tff(c_4131,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_4107,c_4125])).

tff(c_4103,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4092,c_20])).

tff(c_3362,plain,(
    ! [C_3791,B_3792,A_3793] :
      ( r2_hidden(C_3791,B_3792)
      | ~ r2_hidden(C_3791,A_3793)
      | ~ r1_tarski(A_3793,B_3792) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3722,plain,(
    ! [A_3822,B_3823] :
      ( r2_hidden('#skF_2'(A_3822),B_3823)
      | ~ r1_tarski(A_3822,B_3823)
      | k1_xboole_0 = A_3822 ) ),
    inference(resolution,[status(thm)],[c_12,c_3362])).

tff(c_3218,plain,(
    ! [C_29] :
      ( C_29 = '#skF_5'
      | ~ r2_hidden(C_29,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3195,c_32])).

tff(c_5812,plain,(
    ! [A_7906] :
      ( '#skF_2'(A_7906) = '#skF_5'
      | ~ r1_tarski(A_7906,'#skF_6')
      | k1_xboole_0 = A_7906 ) ),
    inference(resolution,[status(thm)],[c_3722,c_3218])).

tff(c_5815,plain,
    ( '#skF_2'('#skF_7') = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_4103,c_5812])).

tff(c_5838,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5815])).

tff(c_5854,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_5838,c_12])).

tff(c_5859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4131,c_5854])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/2.02  
% 5.13/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/2.02  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 5.13/2.02  
% 5.13/2.02  %Foreground sorts:
% 5.13/2.02  
% 5.13/2.02  
% 5.13/2.02  %Background operators:
% 5.13/2.02  
% 5.13/2.02  
% 5.13/2.02  %Foreground operators:
% 5.13/2.02  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.13/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.13/2.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.13/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.13/2.02  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.13/2.02  tff('#skF_7', type, '#skF_7': $i).
% 5.13/2.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.13/2.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.13/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.13/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.13/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.13/2.02  tff('#skF_5', type, '#skF_5': $i).
% 5.13/2.02  tff('#skF_6', type, '#skF_6': $i).
% 5.13/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.13/2.02  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.13/2.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.13/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/2.02  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.13/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.13/2.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.13/2.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.13/2.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.13/2.02  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.13/2.02  
% 5.40/2.04  tff(f_102, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 5.40/2.04  tff(f_54, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.40/2.04  tff(f_58, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.40/2.04  tff(f_60, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.40/2.04  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.40/2.04  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.40/2.04  tff(f_62, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.40/2.04  tff(f_87, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.40/2.04  tff(f_56, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.40/2.04  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.40/2.04  tff(f_44, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.40/2.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.40/2.04  tff(f_69, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.40/2.04  tff(f_52, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.40/2.04  tff(c_64, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.40/2.04  tff(c_68, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.40/2.04  tff(c_22, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.40/2.04  tff(c_3743, plain, (![A_3824, B_3825, C_3826]: (k5_xboole_0(k5_xboole_0(A_3824, B_3825), C_3826)=k5_xboole_0(A_3824, k5_xboole_0(B_3825, C_3826)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.40/2.04  tff(c_28, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.40/2.04  tff(c_3905, plain, (![A_3829, B_3830]: (k5_xboole_0(A_3829, k5_xboole_0(B_3830, k5_xboole_0(A_3829, B_3830)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3743, c_28])).
% 5.40/2.04  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.40/2.04  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.40/2.04  tff(c_3539, plain, (![A_3811, B_3812]: (k5_xboole_0(k5_xboole_0(A_3811, B_3812), k2_xboole_0(A_3811, B_3812))=k3_xboole_0(A_3811, B_3812))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.40/2.04  tff(c_3560, plain, (![A_6]: (k5_xboole_0(k5_xboole_0(A_6, A_6), A_6)=k3_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3539])).
% 5.40/2.04  tff(c_3566, plain, (![A_6]: (k5_xboole_0(k1_xboole_0, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10, c_3560])).
% 5.40/2.04  tff(c_3820, plain, (![A_22, C_3826]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_3826))=k5_xboole_0(k1_xboole_0, C_3826))), inference(superposition, [status(thm), theory('equality')], [c_28, c_3743])).
% 5.40/2.04  tff(c_3833, plain, (![A_22, C_3826]: (k5_xboole_0(A_22, k5_xboole_0(A_22, C_3826))=C_3826)), inference(demodulation, [status(thm), theory('equality')], [c_3566, c_3820])).
% 5.40/2.04  tff(c_3913, plain, (![B_3830, A_3829]: (k5_xboole_0(B_3830, k5_xboole_0(A_3829, B_3830))=k5_xboole_0(A_3829, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3905, c_3833])).
% 5.40/2.04  tff(c_3990, plain, (![B_3830, A_3829]: (k5_xboole_0(B_3830, k5_xboole_0(A_3829, B_3830))=A_3829)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3913])).
% 5.40/2.04  tff(c_66, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.40/2.04  tff(c_60, plain, (![A_58, B_59]: (r1_tarski(k1_tarski(A_58), B_59) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.40/2.04  tff(c_70, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.40/2.04  tff(c_136, plain, (![A_71, B_72]: (r1_tarski(A_71, k2_xboole_0(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.40/2.04  tff(c_139, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_136])).
% 5.40/2.04  tff(c_237, plain, (![B_92, A_93]: (B_92=A_93 | ~r1_tarski(B_92, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.40/2.04  tff(c_249, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_139, c_237])).
% 5.40/2.04  tff(c_256, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_249])).
% 5.40/2.04  tff(c_260, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_256])).
% 5.40/2.04  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.40/2.04  tff(c_270, plain, (![C_97, B_98, A_99]: (r2_hidden(C_97, B_98) | ~r2_hidden(C_97, A_99) | ~r1_tarski(A_99, B_98))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.40/2.04  tff(c_293, plain, (![A_102, B_103]: (r2_hidden('#skF_2'(A_102), B_103) | ~r1_tarski(A_102, B_103) | k1_xboole_0=A_102)), inference(resolution, [status(thm)], [c_12, c_270])).
% 5.40/2.04  tff(c_32, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.40/2.04  tff(c_3152, plain, (![A_3679, A_3680]: (A_3679='#skF_2'(A_3680) | ~r1_tarski(A_3680, k1_tarski(A_3679)) | k1_xboole_0=A_3680)), inference(resolution, [status(thm)], [c_293, c_32])).
% 5.40/2.04  tff(c_3167, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_139, c_3152])).
% 5.40/2.04  tff(c_3180, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_3167])).
% 5.40/2.04  tff(c_3189, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3180, c_12])).
% 5.40/2.04  tff(c_3194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_260, c_3189])).
% 5.40/2.04  tff(c_3195, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_249])).
% 5.40/2.04  tff(c_3198, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3195, c_70])).
% 5.40/2.04  tff(c_3554, plain, (k5_xboole_0(k5_xboole_0('#skF_6', '#skF_7'), '#skF_6')=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3198, c_3539])).
% 5.40/2.04  tff(c_3756, plain, (k5_xboole_0('#skF_6', k5_xboole_0('#skF_7', '#skF_6'))=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3743, c_3554])).
% 5.40/2.04  tff(c_4092, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3990, c_3756])).
% 5.40/2.04  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(k3_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.40/2.04  tff(c_251, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, k3_xboole_0(A_14, B_15)))), inference(resolution, [status(thm)], [c_20, c_237])).
% 5.40/2.04  tff(c_4097, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4092, c_251])).
% 5.40/2.04  tff(c_4106, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4092, c_4097])).
% 5.40/2.04  tff(c_4107, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_68, c_4106])).
% 5.40/2.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.40/2.04  tff(c_3258, plain, (![C_3784]: (C_3784='#skF_5' | ~r2_hidden(C_3784, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3195, c_32])).
% 5.40/2.04  tff(c_3272, plain, (![B_2]: ('#skF_1'('#skF_6', B_2)='#skF_5' | r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_3258])).
% 5.40/2.04  tff(c_4113, plain, ('#skF_1'('#skF_6', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_3272, c_4107])).
% 5.40/2.04  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.40/2.04  tff(c_4125, plain, (~r2_hidden('#skF_5', '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4113, c_4])).
% 5.40/2.04  tff(c_4131, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_4107, c_4125])).
% 5.40/2.04  tff(c_4103, plain, (r1_tarski('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4092, c_20])).
% 5.40/2.04  tff(c_3362, plain, (![C_3791, B_3792, A_3793]: (r2_hidden(C_3791, B_3792) | ~r2_hidden(C_3791, A_3793) | ~r1_tarski(A_3793, B_3792))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.40/2.04  tff(c_3722, plain, (![A_3822, B_3823]: (r2_hidden('#skF_2'(A_3822), B_3823) | ~r1_tarski(A_3822, B_3823) | k1_xboole_0=A_3822)), inference(resolution, [status(thm)], [c_12, c_3362])).
% 5.40/2.04  tff(c_3218, plain, (![C_29]: (C_29='#skF_5' | ~r2_hidden(C_29, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3195, c_32])).
% 5.40/2.04  tff(c_5812, plain, (![A_7906]: ('#skF_2'(A_7906)='#skF_5' | ~r1_tarski(A_7906, '#skF_6') | k1_xboole_0=A_7906)), inference(resolution, [status(thm)], [c_3722, c_3218])).
% 5.40/2.04  tff(c_5815, plain, ('#skF_2'('#skF_7')='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_4103, c_5812])).
% 5.40/2.04  tff(c_5838, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_64, c_5815])).
% 5.40/2.04  tff(c_5854, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_5838, c_12])).
% 5.40/2.04  tff(c_5859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_4131, c_5854])).
% 5.40/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/2.04  
% 5.40/2.04  Inference rules
% 5.40/2.04  ----------------------
% 5.40/2.04  #Ref     : 0
% 5.40/2.04  #Sup     : 1096
% 5.40/2.04  #Fact    : 0
% 5.40/2.04  #Define  : 0
% 5.40/2.04  #Split   : 3
% 5.40/2.04  #Chain   : 0
% 5.40/2.04  #Close   : 0
% 5.40/2.04  
% 5.40/2.04  Ordering : KBO
% 5.40/2.04  
% 5.40/2.04  Simplification rules
% 5.40/2.04  ----------------------
% 5.40/2.04  #Subsume      : 34
% 5.40/2.04  #Demod        : 616
% 5.40/2.04  #Tautology    : 621
% 5.40/2.04  #SimpNegUnit  : 22
% 5.40/2.04  #BackRed      : 7
% 5.40/2.04  
% 5.40/2.04  #Partial instantiations: 3080
% 5.40/2.04  #Strategies tried      : 1
% 5.40/2.04  
% 5.40/2.04  Timing (in seconds)
% 5.40/2.04  ----------------------
% 5.40/2.04  Preprocessing        : 0.36
% 5.40/2.04  Parsing              : 0.19
% 5.40/2.04  CNF conversion       : 0.03
% 5.40/2.04  Main loop            : 0.89
% 5.40/2.04  Inferencing          : 0.39
% 5.40/2.04  Reduction            : 0.28
% 5.40/2.04  Demodulation         : 0.21
% 5.40/2.04  BG Simplification    : 0.04
% 5.40/2.04  Subsumption          : 0.13
% 5.40/2.04  Abstraction          : 0.04
% 5.40/2.04  MUC search           : 0.00
% 5.40/2.04  Cooper               : 0.00
% 5.40/2.04  Total                : 1.29
% 5.40/2.04  Index Insertion      : 0.00
% 5.40/2.04  Index Deletion       : 0.00
% 5.40/2.04  Index Matching       : 0.00
% 5.40/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
