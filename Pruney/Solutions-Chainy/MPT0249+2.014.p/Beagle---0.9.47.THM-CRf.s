%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:25 EST 2020

% Result     : Theorem 5.31s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 190 expanded)
%              Number of leaves         :   40 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          :  117 ( 279 expanded)
%              Number of equality atoms :   59 ( 165 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_64,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_70,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_62,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k1_tarski(A_61),B_62)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_72,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_110,plain,(
    ! [A_72,B_73] : r1_tarski(A_72,k2_xboole_0(A_72,B_73)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_113,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_110])).

tff(c_273,plain,(
    ! [B_95,A_96] :
      ( B_95 = A_96
      | ~ r1_tarski(B_95,A_96)
      | ~ r1_tarski(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_285,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_273])).

tff(c_306,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_310,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_306])).

tff(c_14,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_224,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k1_tarski(A_86),B_87)
      | ~ r2_hidden(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_228,plain,(
    ! [A_86,B_87] :
      ( k2_xboole_0(k1_tarski(A_86),B_87) = B_87
      | ~ r2_hidden(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_224,c_22])).

tff(c_26,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_251,plain,(
    ! [A_91,B_92] :
      ( r2_hidden(A_91,B_92)
      | ~ r1_tarski(k1_tarski(A_91),B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_264,plain,(
    ! [A_91,B_21] : r2_hidden(A_91,k2_xboole_0(k1_tarski(A_91),B_21)) ),
    inference(resolution,[status(thm)],[c_26,c_251])).

tff(c_422,plain,(
    ! [C_109,B_110,A_111] :
      ( r2_hidden(C_109,B_110)
      | ~ r2_hidden(C_109,A_111)
      | ~ r1_tarski(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3709,plain,(
    ! [A_4044,B_4045,B_4046] :
      ( r2_hidden(A_4044,B_4045)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_4044),B_4046),B_4045) ) ),
    inference(resolution,[status(thm)],[c_264,c_422])).

tff(c_3737,plain,(
    ! [A_4097,B_4098,B_4099] : r2_hidden(A_4097,k2_xboole_0(k2_xboole_0(k1_tarski(A_4097),B_4098),B_4099)) ),
    inference(resolution,[status(thm)],[c_26,c_3709])).

tff(c_3819,plain,(
    ! [A_4150,B_4151,B_4152] :
      ( r2_hidden(A_4150,k2_xboole_0(B_4151,B_4152))
      | ~ r2_hidden(A_4150,B_4151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_3737])).

tff(c_3857,plain,(
    ! [A_4203] :
      ( r2_hidden(A_4203,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_4203,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_3819])).

tff(c_34,plain,(
    ! [C_32,A_28] :
      ( C_32 = A_28
      | ~ r2_hidden(C_32,k1_tarski(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3922,plain,(
    ! [A_4254] :
      ( A_4254 = '#skF_5'
      | ~ r2_hidden(A_4254,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3857,c_34])).

tff(c_3938,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_14,c_3922])).

tff(c_3944,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3938])).

tff(c_3951,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3944,c_14])).

tff(c_3956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_310,c_3951])).

tff(c_3957,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_3961,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3957,c_72])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4563,plain,(
    ! [A_4395,B_4396] : k5_xboole_0(k5_xboole_0(A_4395,B_4396),k2_xboole_0(A_4395,B_4396)) = k3_xboole_0(A_4395,B_4396) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4611,plain,(
    ! [A_8] : k5_xboole_0(k5_xboole_0(A_8,A_8),A_8) = k3_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_4563])).

tff(c_4620,plain,(
    ! [A_8] : k5_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12,c_4611])).

tff(c_4793,plain,(
    ! [A_4401,B_4402,C_4403] : k5_xboole_0(k5_xboole_0(A_4401,B_4402),C_4403) = k5_xboole_0(A_4401,k5_xboole_0(B_4402,C_4403)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4879,plain,(
    ! [A_25,C_4403] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_4403)) = k5_xboole_0(k1_xboole_0,C_4403) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4793])).

tff(c_4895,plain,(
    ! [A_4404,C_4405] : k5_xboole_0(A_4404,k5_xboole_0(A_4404,C_4405)) = C_4405 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4620,c_4879])).

tff(c_4969,plain,(
    ! [A_4406,B_4407] : k5_xboole_0(A_4406,k5_xboole_0(B_4407,A_4406)) = B_4407 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4895])).

tff(c_4950,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4895])).

tff(c_4972,plain,(
    ! [B_4407,A_4406] : k5_xboole_0(k5_xboole_0(B_4407,A_4406),B_4407) = A_4406 ),
    inference(superposition,[status(thm),theory(equality)],[c_4969,c_4950])).

tff(c_4593,plain,(
    k5_xboole_0(k5_xboole_0('#skF_6','#skF_7'),'#skF_6') = k3_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3961,c_4563])).

tff(c_5093,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4972,c_4593])).

tff(c_24,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5209,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5093,c_24])).

tff(c_4342,plain,(
    ! [C_4376,B_4377,A_4378] :
      ( r2_hidden(C_4376,B_4377)
      | ~ r2_hidden(C_4376,A_4378)
      | ~ r1_tarski(A_4378,B_4377) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4542,plain,(
    ! [A_4393,B_4394] :
      ( r2_hidden('#skF_2'(A_4393),B_4394)
      | ~ r1_tarski(A_4393,B_4394)
      | k1_xboole_0 = A_4393 ) ),
    inference(resolution,[status(thm)],[c_14,c_4342])).

tff(c_3982,plain,(
    ! [C_32] :
      ( C_32 = '#skF_5'
      | ~ r2_hidden(C_32,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3957,c_34])).

tff(c_6751,plain,(
    ! [A_8630] :
      ( '#skF_2'(A_8630) = '#skF_5'
      | ~ r1_tarski(A_8630,'#skF_6')
      | k1_xboole_0 = A_8630 ) ),
    inference(resolution,[status(thm)],[c_4542,c_3982])).

tff(c_6754,plain,
    ( '#skF_2'('#skF_7') = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5209,c_6751])).

tff(c_6777,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6754])).

tff(c_6793,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_6777,c_14])).

tff(c_6797,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_6793])).

tff(c_4252,plain,(
    ! [A_4370,B_4371] :
      ( k2_xboole_0(k1_tarski(A_4370),B_4371) = B_4371
      | ~ r2_hidden(A_4370,B_4371) ) ),
    inference(resolution,[status(thm)],[c_224,c_22])).

tff(c_4282,plain,(
    ! [B_4371] :
      ( k2_xboole_0('#skF_6',B_4371) = B_4371
      | ~ r2_hidden('#skF_5',B_4371) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3957,c_4252])).

tff(c_6803,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6797,c_4282])).

tff(c_6809,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3961,c_6803])).

tff(c_6811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.31/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.00  
% 5.31/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.00  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 5.31/2.00  
% 5.31/2.00  %Foreground sorts:
% 5.31/2.00  
% 5.31/2.00  
% 5.31/2.00  %Background operators:
% 5.31/2.00  
% 5.31/2.00  
% 5.31/2.00  %Foreground operators:
% 5.31/2.00  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.31/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.31/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.31/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.31/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.31/2.00  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.31/2.00  tff('#skF_7', type, '#skF_7': $i).
% 5.31/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.31/2.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.31/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.31/2.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.31/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.31/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.31/2.00  tff('#skF_6', type, '#skF_6': $i).
% 5.31/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.31/2.00  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.31/2.00  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.31/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.31/2.00  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.31/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.31/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.31/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.31/2.00  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.31/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.31/2.00  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.31/2.00  
% 5.31/2.02  tff(f_106, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 5.31/2.02  tff(f_91, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.31/2.02  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.31/2.02  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.31/2.02  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.31/2.02  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.31/2.02  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.31/2.02  tff(f_73, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.31/2.02  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.31/2.02  tff(f_64, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.31/2.02  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.31/2.02  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.31/2.02  tff(f_66, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.31/2.02  tff(f_62, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.31/2.02  tff(f_58, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.31/2.02  tff(c_70, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.31/2.02  tff(c_68, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.31/2.02  tff(c_62, plain, (![A_61, B_62]: (r1_tarski(k1_tarski(A_61), B_62) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.31/2.02  tff(c_72, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.31/2.02  tff(c_110, plain, (![A_72, B_73]: (r1_tarski(A_72, k2_xboole_0(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.31/2.02  tff(c_113, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_110])).
% 5.31/2.02  tff(c_273, plain, (![B_95, A_96]: (B_95=A_96 | ~r1_tarski(B_95, A_96) | ~r1_tarski(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.31/2.02  tff(c_285, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_113, c_273])).
% 5.31/2.02  tff(c_306, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_285])).
% 5.31/2.02  tff(c_310, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_306])).
% 5.31/2.02  tff(c_14, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.31/2.02  tff(c_224, plain, (![A_86, B_87]: (r1_tarski(k1_tarski(A_86), B_87) | ~r2_hidden(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.31/2.02  tff(c_22, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.31/2.02  tff(c_228, plain, (![A_86, B_87]: (k2_xboole_0(k1_tarski(A_86), B_87)=B_87 | ~r2_hidden(A_86, B_87))), inference(resolution, [status(thm)], [c_224, c_22])).
% 5.31/2.02  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.31/2.02  tff(c_251, plain, (![A_91, B_92]: (r2_hidden(A_91, B_92) | ~r1_tarski(k1_tarski(A_91), B_92))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.31/2.02  tff(c_264, plain, (![A_91, B_21]: (r2_hidden(A_91, k2_xboole_0(k1_tarski(A_91), B_21)))), inference(resolution, [status(thm)], [c_26, c_251])).
% 5.31/2.02  tff(c_422, plain, (![C_109, B_110, A_111]: (r2_hidden(C_109, B_110) | ~r2_hidden(C_109, A_111) | ~r1_tarski(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.31/2.02  tff(c_3709, plain, (![A_4044, B_4045, B_4046]: (r2_hidden(A_4044, B_4045) | ~r1_tarski(k2_xboole_0(k1_tarski(A_4044), B_4046), B_4045))), inference(resolution, [status(thm)], [c_264, c_422])).
% 5.31/2.02  tff(c_3737, plain, (![A_4097, B_4098, B_4099]: (r2_hidden(A_4097, k2_xboole_0(k2_xboole_0(k1_tarski(A_4097), B_4098), B_4099)))), inference(resolution, [status(thm)], [c_26, c_3709])).
% 5.31/2.02  tff(c_3819, plain, (![A_4150, B_4151, B_4152]: (r2_hidden(A_4150, k2_xboole_0(B_4151, B_4152)) | ~r2_hidden(A_4150, B_4151))), inference(superposition, [status(thm), theory('equality')], [c_228, c_3737])).
% 5.31/2.02  tff(c_3857, plain, (![A_4203]: (r2_hidden(A_4203, k1_tarski('#skF_5')) | ~r2_hidden(A_4203, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_3819])).
% 5.31/2.02  tff(c_34, plain, (![C_32, A_28]: (C_32=A_28 | ~r2_hidden(C_32, k1_tarski(A_28)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.31/2.02  tff(c_3922, plain, (![A_4254]: (A_4254='#skF_5' | ~r2_hidden(A_4254, '#skF_6'))), inference(resolution, [status(thm)], [c_3857, c_34])).
% 5.31/2.02  tff(c_3938, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_14, c_3922])).
% 5.31/2.02  tff(c_3944, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_68, c_3938])).
% 5.31/2.02  tff(c_3951, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3944, c_14])).
% 5.31/2.02  tff(c_3956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_310, c_3951])).
% 5.31/2.02  tff(c_3957, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_285])).
% 5.31/2.02  tff(c_3961, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3957, c_72])).
% 5.31/2.02  tff(c_66, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.31/2.02  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.31/2.02  tff(c_30, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.31/2.02  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.31/2.02  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.31/2.02  tff(c_4563, plain, (![A_4395, B_4396]: (k5_xboole_0(k5_xboole_0(A_4395, B_4396), k2_xboole_0(A_4395, B_4396))=k3_xboole_0(A_4395, B_4396))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.31/2.02  tff(c_4611, plain, (![A_8]: (k5_xboole_0(k5_xboole_0(A_8, A_8), A_8)=k3_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_4563])).
% 5.31/2.02  tff(c_4620, plain, (![A_8]: (k5_xboole_0(k1_xboole_0, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12, c_4611])).
% 5.31/2.02  tff(c_4793, plain, (![A_4401, B_4402, C_4403]: (k5_xboole_0(k5_xboole_0(A_4401, B_4402), C_4403)=k5_xboole_0(A_4401, k5_xboole_0(B_4402, C_4403)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.31/2.02  tff(c_4879, plain, (![A_25, C_4403]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_4403))=k5_xboole_0(k1_xboole_0, C_4403))), inference(superposition, [status(thm), theory('equality')], [c_30, c_4793])).
% 5.31/2.02  tff(c_4895, plain, (![A_4404, C_4405]: (k5_xboole_0(A_4404, k5_xboole_0(A_4404, C_4405))=C_4405)), inference(demodulation, [status(thm), theory('equality')], [c_4620, c_4879])).
% 5.31/2.02  tff(c_4969, plain, (![A_4406, B_4407]: (k5_xboole_0(A_4406, k5_xboole_0(B_4407, A_4406))=B_4407)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4895])).
% 5.31/2.02  tff(c_4950, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4895])).
% 5.31/2.02  tff(c_4972, plain, (![B_4407, A_4406]: (k5_xboole_0(k5_xboole_0(B_4407, A_4406), B_4407)=A_4406)), inference(superposition, [status(thm), theory('equality')], [c_4969, c_4950])).
% 5.31/2.02  tff(c_4593, plain, (k5_xboole_0(k5_xboole_0('#skF_6', '#skF_7'), '#skF_6')=k3_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3961, c_4563])).
% 5.31/2.02  tff(c_5093, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_4972, c_4593])).
% 5.31/2.02  tff(c_24, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.31/2.02  tff(c_5209, plain, (r1_tarski('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5093, c_24])).
% 5.31/2.02  tff(c_4342, plain, (![C_4376, B_4377, A_4378]: (r2_hidden(C_4376, B_4377) | ~r2_hidden(C_4376, A_4378) | ~r1_tarski(A_4378, B_4377))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.31/2.02  tff(c_4542, plain, (![A_4393, B_4394]: (r2_hidden('#skF_2'(A_4393), B_4394) | ~r1_tarski(A_4393, B_4394) | k1_xboole_0=A_4393)), inference(resolution, [status(thm)], [c_14, c_4342])).
% 5.31/2.02  tff(c_3982, plain, (![C_32]: (C_32='#skF_5' | ~r2_hidden(C_32, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3957, c_34])).
% 5.31/2.02  tff(c_6751, plain, (![A_8630]: ('#skF_2'(A_8630)='#skF_5' | ~r1_tarski(A_8630, '#skF_6') | k1_xboole_0=A_8630)), inference(resolution, [status(thm)], [c_4542, c_3982])).
% 5.31/2.02  tff(c_6754, plain, ('#skF_2'('#skF_7')='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_5209, c_6751])).
% 5.31/2.02  tff(c_6777, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_6754])).
% 5.31/2.02  tff(c_6793, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_6777, c_14])).
% 5.31/2.02  tff(c_6797, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_66, c_6793])).
% 5.31/2.02  tff(c_4252, plain, (![A_4370, B_4371]: (k2_xboole_0(k1_tarski(A_4370), B_4371)=B_4371 | ~r2_hidden(A_4370, B_4371))), inference(resolution, [status(thm)], [c_224, c_22])).
% 5.31/2.02  tff(c_4282, plain, (![B_4371]: (k2_xboole_0('#skF_6', B_4371)=B_4371 | ~r2_hidden('#skF_5', B_4371))), inference(superposition, [status(thm), theory('equality')], [c_3957, c_4252])).
% 5.31/2.02  tff(c_6803, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_6797, c_4282])).
% 5.31/2.02  tff(c_6809, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3961, c_6803])).
% 5.31/2.02  tff(c_6811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_6809])).
% 5.31/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/2.02  
% 5.31/2.02  Inference rules
% 5.31/2.02  ----------------------
% 5.31/2.02  #Ref     : 0
% 5.31/2.02  #Sup     : 1271
% 5.31/2.02  #Fact    : 0
% 5.31/2.02  #Define  : 0
% 5.31/2.02  #Split   : 3
% 5.31/2.02  #Chain   : 0
% 5.31/2.02  #Close   : 0
% 5.31/2.02  
% 5.31/2.02  Ordering : KBO
% 5.31/2.02  
% 5.31/2.02  Simplification rules
% 5.31/2.02  ----------------------
% 5.31/2.02  #Subsume      : 46
% 5.31/2.02  #Demod        : 789
% 5.31/2.02  #Tautology    : 733
% 5.31/2.02  #SimpNegUnit  : 24
% 5.31/2.02  #BackRed      : 9
% 5.31/2.02  
% 5.31/2.02  #Partial instantiations: 3380
% 5.31/2.02  #Strategies tried      : 1
% 5.31/2.02  
% 5.31/2.02  Timing (in seconds)
% 5.31/2.02  ----------------------
% 5.31/2.02  Preprocessing        : 0.33
% 5.31/2.02  Parsing              : 0.17
% 5.31/2.02  CNF conversion       : 0.02
% 5.31/2.02  Main loop            : 0.93
% 5.31/2.02  Inferencing          : 0.39
% 5.31/2.02  Reduction            : 0.32
% 5.31/2.02  Demodulation         : 0.25
% 5.31/2.02  BG Simplification    : 0.04
% 5.31/2.02  Subsumption          : 0.12
% 5.31/2.02  Abstraction          : 0.04
% 5.31/2.02  MUC search           : 0.00
% 5.31/2.02  Cooper               : 0.00
% 5.31/2.02  Total                : 1.29
% 5.31/2.02  Index Insertion      : 0.00
% 5.31/2.02  Index Deletion       : 0.00
% 5.31/2.02  Index Matching       : 0.00
% 5.31/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
