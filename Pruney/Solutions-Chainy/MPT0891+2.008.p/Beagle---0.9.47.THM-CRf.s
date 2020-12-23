%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:41 EST 2020

% Result     : Theorem 50.25s
% Output     : CNFRefutation 50.37s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 192 expanded)
%              Number of leaves         :   41 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  169 ( 446 expanded)
%              Number of equality atoms :  134 ( 350 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_95,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_68,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_131,axiom,(
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

tff(f_111,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_42,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_279980,plain,(
    ! [B_214832,A_214833] :
      ( ~ r2_hidden(B_214832,A_214833)
      | k4_xboole_0(A_214833,k1_tarski(B_214832)) != A_214833 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_279985,plain,(
    ! [B_214832] : ~ r2_hidden(B_214832,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_279980])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_280033,plain,(
    ! [B_214840,C_214841,A_214842] :
      ( r2_hidden(B_214840,C_214841)
      | k4_xboole_0(k2_tarski(A_214842,B_214840),C_214841) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_280044,plain,(
    ! [B_214840,A_214842] :
      ( r2_hidden(B_214840,k1_xboole_0)
      | k2_tarski(A_214842,B_214840) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_280033])).

tff(c_280046,plain,(
    ! [A_214843,B_214844] : k2_tarski(A_214843,B_214844) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_279985,c_280044])).

tff(c_280048,plain,(
    ! [A_15] : k1_tarski(A_15) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_280046])).

tff(c_64,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_5'(A_34),A_34)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_153,plain,(
    ! [C_83,A_84] :
      ( C_83 = A_84
      | ~ r2_hidden(C_83,k1_tarski(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_161,plain,(
    ! [A_84] :
      ( '#skF_5'(k1_tarski(A_84)) = A_84
      | k1_tarski(A_84) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_64,c_153])).

tff(c_280062,plain,(
    ! [A_84] : '#skF_5'(k1_tarski(A_84)) = A_84 ),
    inference(negUnitSimplification,[status(thm)],[c_280048,c_161])).

tff(c_32,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_280580,plain,(
    ! [D_216762,A_216763,C_216764,E_216765] :
      ( ~ r2_hidden(D_216762,A_216763)
      | k3_mcart_1(C_216764,D_216762,E_216765) != '#skF_5'(A_216763)
      | k1_xboole_0 = A_216763 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_280594,plain,(
    ! [C_216764,C_14,E_216765] :
      ( k3_mcart_1(C_216764,C_14,E_216765) != '#skF_5'(k1_tarski(C_14))
      | k1_tarski(C_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_280580])).

tff(c_280606,plain,(
    ! [C_216764,C_14,E_216765] :
      ( k3_mcart_1(C_216764,C_14,E_216765) != C_14
      | k1_tarski(C_14) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280062,c_280594])).

tff(c_280607,plain,(
    ! [C_216764,C_14,E_216765] : k3_mcart_1(C_216764,C_14,E_216765) != C_14 ),
    inference(negUnitSimplification,[status(thm)],[c_280048,c_280606])).

tff(c_84,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_132160,plain,(
    ! [A_99579,B_99580,C_99581] : k4_tarski(k4_tarski(A_99579,B_99580),C_99581) = k3_mcart_1(A_99579,B_99580,C_99581) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_80,plain,(
    ! [A_58,B_59] : k2_mcart_1(k4_tarski(A_58,B_59)) = B_59 ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_60,plain,(
    ! [B_32,C_33] : k2_mcart_1(k4_tarski(B_32,C_33)) != k4_tarski(B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_92,plain,(
    ! [B_32,C_33] : k4_tarski(B_32,C_33) != C_33 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_60])).

tff(c_132178,plain,(
    ! [A_99579,B_99580,C_99581] : k3_mcart_1(A_99579,B_99580,C_99581) != C_99581 ),
    inference(superposition,[status(thm),theory(equality)],[c_132160,c_92])).

tff(c_231,plain,(
    ! [B_94,A_95] :
      ( ~ r2_hidden(B_94,A_95)
      | k4_xboole_0(A_95,k1_tarski(B_94)) != A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_240,plain,(
    ! [B_94] : ~ r2_hidden(B_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_231])).

tff(c_248,plain,(
    ! [B_97,C_98,A_99] :
      ( r2_hidden(B_97,C_98)
      | k4_xboole_0(k2_tarski(A_99,B_97),C_98) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_259,plain,(
    ! [B_97,A_99] :
      ( r2_hidden(B_97,k1_xboole_0)
      | k2_tarski(A_99,B_97) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_248])).

tff(c_261,plain,(
    ! [A_100,B_101] : k2_tarski(A_100,B_101) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_259])).

tff(c_263,plain,(
    ! [A_15] : k1_tarski(A_15) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_261])).

tff(c_291,plain,(
    ! [A_84] : '#skF_5'(k1_tarski(A_84)) = A_84 ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_161])).

tff(c_811,plain,(
    ! [C_2092,A_2093,D_2094,E_2095] :
      ( ~ r2_hidden(C_2092,A_2093)
      | k3_mcart_1(C_2092,D_2094,E_2095) != '#skF_5'(A_2093)
      | k1_xboole_0 = A_2093 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_825,plain,(
    ! [C_14,D_2094,E_2095] :
      ( k3_mcart_1(C_14,D_2094,E_2095) != '#skF_5'(k1_tarski(C_14))
      | k1_tarski(C_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_811])).

tff(c_837,plain,(
    ! [C_14,D_2094,E_2095] :
      ( k3_mcart_1(C_14,D_2094,E_2095) != C_14
      | k1_tarski(C_14) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_825])).

tff(c_838,plain,(
    ! [C_14,D_2094,E_2095] : k3_mcart_1(C_14,D_2094,E_2095) != C_14 ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_837])).

tff(c_82,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_187,plain,(
    k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_5576,plain,(
    ! [A_30428,B_30429,C_30430,D_30431] :
      ( k7_mcart_1(A_30428,B_30429,C_30430,D_30431) = k2_mcart_1(D_30431)
      | ~ m1_subset_1(D_30431,k3_zfmisc_1(A_30428,B_30429,C_30430))
      | k1_xboole_0 = C_30430
      | k1_xboole_0 = B_30429
      | k1_xboole_0 = A_30428 ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5588,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_84,c_5576])).

tff(c_5591,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_88,c_86,c_5588])).

tff(c_128165,plain,(
    ! [A_98937,B_98938,C_98939,D_98940] :
      ( k3_mcart_1(k5_mcart_1(A_98937,B_98938,C_98939,D_98940),k6_mcart_1(A_98937,B_98938,C_98939,D_98940),k7_mcart_1(A_98937,B_98938,C_98939,D_98940)) = D_98940
      | ~ m1_subset_1(D_98940,k3_zfmisc_1(A_98937,B_98938,C_98939))
      | k1_xboole_0 = C_98939
      | k1_xboole_0 = B_98938
      | k1_xboole_0 = A_98937 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_132047,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_5591,c_128165])).

tff(c_132092,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_187,c_132047])).

tff(c_132094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_88,c_86,c_838,c_132092])).

tff(c_132095,plain,
    ( k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_132103,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_132095])).

tff(c_276019,plain,(
    ! [A_214197,B_214198,C_214199,D_214200] :
      ( k3_mcart_1(k5_mcart_1(A_214197,B_214198,C_214199,D_214200),k6_mcart_1(A_214197,B_214198,C_214199,D_214200),k7_mcart_1(A_214197,B_214198,C_214199,D_214200)) = D_214200
      | ~ m1_subset_1(D_214200,k3_zfmisc_1(A_214197,B_214198,C_214199))
      | k1_xboole_0 = C_214199
      | k1_xboole_0 = B_214198
      | k1_xboole_0 = A_214197 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_279937,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_132103,c_276019])).

tff(c_279957,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_279937])).

tff(c_279959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_88,c_86,c_132178,c_279957])).

tff(c_279960,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_132095])).

tff(c_284987,plain,(
    ! [A_244105,B_244106,C_244107,D_244108] :
      ( k7_mcart_1(A_244105,B_244106,C_244107,D_244108) = k2_mcart_1(D_244108)
      | ~ m1_subset_1(D_244108,k3_zfmisc_1(A_244105,B_244106,C_244107))
      | k1_xboole_0 = C_244107
      | k1_xboole_0 = B_244106
      | k1_xboole_0 = A_244105 ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_284999,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_84,c_284987])).

tff(c_285002,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_88,c_86,c_284999])).

tff(c_409021,plain,(
    ! [A_318138,B_318139,C_318140,D_318141] :
      ( k3_mcart_1(k5_mcart_1(A_318138,B_318139,C_318140,D_318141),k6_mcart_1(A_318138,B_318139,C_318140,D_318141),k7_mcart_1(A_318138,B_318139,C_318140,D_318141)) = D_318141
      | ~ m1_subset_1(D_318141,k3_zfmisc_1(A_318138,B_318139,C_318140))
      | k1_xboole_0 = C_318140
      | k1_xboole_0 = B_318139
      | k1_xboole_0 = A_318138 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_412909,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_285002,c_409021])).

tff(c_412954,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_279960,c_412909])).

tff(c_412956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_88,c_86,c_280607,c_412954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:56:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 50.25/35.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.25/35.26  
% 50.25/35.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.25/35.26  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4
% 50.25/35.26  
% 50.25/35.26  %Foreground sorts:
% 50.25/35.26  
% 50.25/35.26  
% 50.25/35.26  %Background operators:
% 50.25/35.26  
% 50.25/35.26  
% 50.25/35.26  %Foreground operators:
% 50.25/35.26  tff('#skF_5', type, '#skF_5': $i > $i).
% 50.25/35.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 50.25/35.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 50.25/35.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 50.25/35.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 50.25/35.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 50.25/35.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 50.25/35.26  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 50.25/35.26  tff('#skF_7', type, '#skF_7': $i).
% 50.25/35.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 50.25/35.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 50.25/35.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 50.25/35.26  tff('#skF_6', type, '#skF_6': $i).
% 50.25/35.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 50.25/35.26  tff('#skF_9', type, '#skF_9': $i).
% 50.25/35.26  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 50.25/35.26  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 50.25/35.26  tff('#skF_8', type, '#skF_8': $i).
% 50.25/35.26  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 50.25/35.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 50.25/35.26  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 50.25/35.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 50.25/35.26  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 50.25/35.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 50.25/35.26  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 50.25/35.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 50.25/35.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 50.25/35.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 50.25/35.26  
% 50.37/35.28  tff(f_159, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 50.37/35.28  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 50.37/35.28  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 50.37/35.28  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 50.37/35.28  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 50.37/35.28  tff(f_66, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 50.37/35.28  tff(f_95, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 50.37/35.28  tff(f_51, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 50.37/35.28  tff(f_68, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 50.37/35.28  tff(f_135, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 50.37/35.28  tff(f_79, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 50.37/35.28  tff(f_131, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 50.37/35.28  tff(f_111, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 50.37/35.28  tff(c_90, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_159])).
% 50.37/35.28  tff(c_88, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_159])).
% 50.37/35.28  tff(c_86, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_159])).
% 50.37/35.28  tff(c_42, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 50.37/35.28  tff(c_4, plain, (![A_2]: (k4_xboole_0(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 50.37/35.28  tff(c_279980, plain, (![B_214832, A_214833]: (~r2_hidden(B_214832, A_214833) | k4_xboole_0(A_214833, k1_tarski(B_214832))!=A_214833)), inference(cnfTransformation, [status(thm)], [f_60])).
% 50.37/35.28  tff(c_279985, plain, (![B_214832]: (~r2_hidden(B_214832, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_279980])).
% 50.37/35.28  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 50.37/35.28  tff(c_280033, plain, (![B_214840, C_214841, A_214842]: (r2_hidden(B_214840, C_214841) | k4_xboole_0(k2_tarski(A_214842, B_214840), C_214841)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 50.37/35.28  tff(c_280044, plain, (![B_214840, A_214842]: (r2_hidden(B_214840, k1_xboole_0) | k2_tarski(A_214842, B_214840)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_280033])).
% 50.37/35.28  tff(c_280046, plain, (![A_214843, B_214844]: (k2_tarski(A_214843, B_214844)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_279985, c_280044])).
% 50.37/35.28  tff(c_280048, plain, (![A_15]: (k1_tarski(A_15)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_280046])).
% 50.37/35.28  tff(c_64, plain, (![A_34]: (r2_hidden('#skF_5'(A_34), A_34) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_95])).
% 50.37/35.28  tff(c_153, plain, (![C_83, A_84]: (C_83=A_84 | ~r2_hidden(C_83, k1_tarski(A_84)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 50.37/35.28  tff(c_161, plain, (![A_84]: ('#skF_5'(k1_tarski(A_84))=A_84 | k1_tarski(A_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_153])).
% 50.37/35.28  tff(c_280062, plain, (![A_84]: ('#skF_5'(k1_tarski(A_84))=A_84)), inference(negUnitSimplification, [status(thm)], [c_280048, c_161])).
% 50.37/35.28  tff(c_32, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 50.37/35.28  tff(c_280580, plain, (![D_216762, A_216763, C_216764, E_216765]: (~r2_hidden(D_216762, A_216763) | k3_mcart_1(C_216764, D_216762, E_216765)!='#skF_5'(A_216763) | k1_xboole_0=A_216763)), inference(cnfTransformation, [status(thm)], [f_95])).
% 50.37/35.28  tff(c_280594, plain, (![C_216764, C_14, E_216765]: (k3_mcart_1(C_216764, C_14, E_216765)!='#skF_5'(k1_tarski(C_14)) | k1_tarski(C_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_280580])).
% 50.37/35.28  tff(c_280606, plain, (![C_216764, C_14, E_216765]: (k3_mcart_1(C_216764, C_14, E_216765)!=C_14 | k1_tarski(C_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_280062, c_280594])).
% 50.37/35.28  tff(c_280607, plain, (![C_216764, C_14, E_216765]: (k3_mcart_1(C_216764, C_14, E_216765)!=C_14)), inference(negUnitSimplification, [status(thm)], [c_280048, c_280606])).
% 50.37/35.28  tff(c_84, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 50.37/35.28  tff(c_132160, plain, (![A_99579, B_99580, C_99581]: (k4_tarski(k4_tarski(A_99579, B_99580), C_99581)=k3_mcart_1(A_99579, B_99580, C_99581))), inference(cnfTransformation, [status(thm)], [f_68])).
% 50.37/35.28  tff(c_80, plain, (![A_58, B_59]: (k2_mcart_1(k4_tarski(A_58, B_59))=B_59)), inference(cnfTransformation, [status(thm)], [f_135])).
% 50.37/35.28  tff(c_60, plain, (![B_32, C_33]: (k2_mcart_1(k4_tarski(B_32, C_33))!=k4_tarski(B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_79])).
% 50.37/35.28  tff(c_92, plain, (![B_32, C_33]: (k4_tarski(B_32, C_33)!=C_33)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_60])).
% 50.37/35.28  tff(c_132178, plain, (![A_99579, B_99580, C_99581]: (k3_mcart_1(A_99579, B_99580, C_99581)!=C_99581)), inference(superposition, [status(thm), theory('equality')], [c_132160, c_92])).
% 50.37/35.28  tff(c_231, plain, (![B_94, A_95]: (~r2_hidden(B_94, A_95) | k4_xboole_0(A_95, k1_tarski(B_94))!=A_95)), inference(cnfTransformation, [status(thm)], [f_60])).
% 50.37/35.28  tff(c_240, plain, (![B_94]: (~r2_hidden(B_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_231])).
% 50.37/35.28  tff(c_248, plain, (![B_97, C_98, A_99]: (r2_hidden(B_97, C_98) | k4_xboole_0(k2_tarski(A_99, B_97), C_98)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 50.37/35.28  tff(c_259, plain, (![B_97, A_99]: (r2_hidden(B_97, k1_xboole_0) | k2_tarski(A_99, B_97)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_248])).
% 50.37/35.28  tff(c_261, plain, (![A_100, B_101]: (k2_tarski(A_100, B_101)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_240, c_259])).
% 50.37/35.28  tff(c_263, plain, (![A_15]: (k1_tarski(A_15)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_261])).
% 50.37/35.28  tff(c_291, plain, (![A_84]: ('#skF_5'(k1_tarski(A_84))=A_84)), inference(negUnitSimplification, [status(thm)], [c_263, c_161])).
% 50.37/35.28  tff(c_811, plain, (![C_2092, A_2093, D_2094, E_2095]: (~r2_hidden(C_2092, A_2093) | k3_mcart_1(C_2092, D_2094, E_2095)!='#skF_5'(A_2093) | k1_xboole_0=A_2093)), inference(cnfTransformation, [status(thm)], [f_95])).
% 50.37/35.28  tff(c_825, plain, (![C_14, D_2094, E_2095]: (k3_mcart_1(C_14, D_2094, E_2095)!='#skF_5'(k1_tarski(C_14)) | k1_tarski(C_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_811])).
% 50.37/35.28  tff(c_837, plain, (![C_14, D_2094, E_2095]: (k3_mcart_1(C_14, D_2094, E_2095)!=C_14 | k1_tarski(C_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_291, c_825])).
% 50.37/35.28  tff(c_838, plain, (![C_14, D_2094, E_2095]: (k3_mcart_1(C_14, D_2094, E_2095)!=C_14)), inference(negUnitSimplification, [status(thm)], [c_263, c_837])).
% 50.37/35.28  tff(c_82, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_159])).
% 50.37/35.28  tff(c_187, plain, (k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_82])).
% 50.37/35.28  tff(c_5576, plain, (![A_30428, B_30429, C_30430, D_30431]: (k7_mcart_1(A_30428, B_30429, C_30430, D_30431)=k2_mcart_1(D_30431) | ~m1_subset_1(D_30431, k3_zfmisc_1(A_30428, B_30429, C_30430)) | k1_xboole_0=C_30430 | k1_xboole_0=B_30429 | k1_xboole_0=A_30428)), inference(cnfTransformation, [status(thm)], [f_131])).
% 50.37/35.28  tff(c_5588, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_84, c_5576])).
% 50.37/35.28  tff(c_5591, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_90, c_88, c_86, c_5588])).
% 50.37/35.28  tff(c_128165, plain, (![A_98937, B_98938, C_98939, D_98940]: (k3_mcart_1(k5_mcart_1(A_98937, B_98938, C_98939, D_98940), k6_mcart_1(A_98937, B_98938, C_98939, D_98940), k7_mcart_1(A_98937, B_98938, C_98939, D_98940))=D_98940 | ~m1_subset_1(D_98940, k3_zfmisc_1(A_98937, B_98938, C_98939)) | k1_xboole_0=C_98939 | k1_xboole_0=B_98938 | k1_xboole_0=A_98937)), inference(cnfTransformation, [status(thm)], [f_111])).
% 50.37/35.28  tff(c_132047, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_5591, c_128165])).
% 50.37/35.28  tff(c_132092, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_187, c_132047])).
% 50.37/35.28  tff(c_132094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_88, c_86, c_838, c_132092])).
% 50.37/35.28  tff(c_132095, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_82])).
% 50.37/35.28  tff(c_132103, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_132095])).
% 50.37/35.28  tff(c_276019, plain, (![A_214197, B_214198, C_214199, D_214200]: (k3_mcart_1(k5_mcart_1(A_214197, B_214198, C_214199, D_214200), k6_mcart_1(A_214197, B_214198, C_214199, D_214200), k7_mcart_1(A_214197, B_214198, C_214199, D_214200))=D_214200 | ~m1_subset_1(D_214200, k3_zfmisc_1(A_214197, B_214198, C_214199)) | k1_xboole_0=C_214199 | k1_xboole_0=B_214198 | k1_xboole_0=A_214197)), inference(cnfTransformation, [status(thm)], [f_111])).
% 50.37/35.28  tff(c_279937, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_132103, c_276019])).
% 50.37/35.28  tff(c_279957, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_279937])).
% 50.37/35.28  tff(c_279959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_88, c_86, c_132178, c_279957])).
% 50.37/35.28  tff(c_279960, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_132095])).
% 50.37/35.28  tff(c_284987, plain, (![A_244105, B_244106, C_244107, D_244108]: (k7_mcart_1(A_244105, B_244106, C_244107, D_244108)=k2_mcart_1(D_244108) | ~m1_subset_1(D_244108, k3_zfmisc_1(A_244105, B_244106, C_244107)) | k1_xboole_0=C_244107 | k1_xboole_0=B_244106 | k1_xboole_0=A_244105)), inference(cnfTransformation, [status(thm)], [f_131])).
% 50.37/35.28  tff(c_284999, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_84, c_284987])).
% 50.37/35.28  tff(c_285002, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_90, c_88, c_86, c_284999])).
% 50.37/35.28  tff(c_409021, plain, (![A_318138, B_318139, C_318140, D_318141]: (k3_mcart_1(k5_mcart_1(A_318138, B_318139, C_318140, D_318141), k6_mcart_1(A_318138, B_318139, C_318140, D_318141), k7_mcart_1(A_318138, B_318139, C_318140, D_318141))=D_318141 | ~m1_subset_1(D_318141, k3_zfmisc_1(A_318138, B_318139, C_318140)) | k1_xboole_0=C_318140 | k1_xboole_0=B_318139 | k1_xboole_0=A_318138)), inference(cnfTransformation, [status(thm)], [f_111])).
% 50.37/35.28  tff(c_412909, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_285002, c_409021])).
% 50.37/35.28  tff(c_412954, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_279960, c_412909])).
% 50.37/35.28  tff(c_412956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_88, c_86, c_280607, c_412954])).
% 50.37/35.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.37/35.28  
% 50.37/35.28  Inference rules
% 50.37/35.28  ----------------------
% 50.37/35.28  #Ref     : 27
% 50.37/35.28  #Sup     : 46126
% 50.37/35.28  #Fact    : 6
% 50.37/35.28  #Define  : 0
% 50.37/35.28  #Split   : 33
% 50.37/35.28  #Chain   : 0
% 50.37/35.28  #Close   : 0
% 50.37/35.28  
% 50.37/35.28  Ordering : KBO
% 50.37/35.28  
% 50.37/35.28  Simplification rules
% 50.37/35.28  ----------------------
% 50.37/35.28  #Subsume      : 7318
% 50.37/35.28  #Demod        : 20752
% 50.37/35.28  #Tautology    : 788
% 50.37/35.28  #SimpNegUnit  : 830
% 50.37/35.28  #BackRed      : 110
% 50.37/35.28  
% 50.37/35.28  #Partial instantiations: 134750
% 50.37/35.28  #Strategies tried      : 1
% 50.37/35.28  
% 50.37/35.28  Timing (in seconds)
% 50.37/35.28  ----------------------
% 50.37/35.28  Preprocessing        : 0.36
% 50.37/35.28  Parsing              : 0.19
% 50.37/35.28  CNF conversion       : 0.03
% 50.37/35.28  Main loop            : 34.12
% 50.37/35.28  Inferencing          : 10.37
% 50.37/35.28  Reduction            : 9.28
% 50.37/35.28  Demodulation         : 6.40
% 50.37/35.28  BG Simplification    : 1.83
% 50.37/35.28  Subsumption          : 11.62
% 50.37/35.28  Abstraction          : 2.85
% 50.37/35.28  MUC search           : 0.00
% 50.37/35.28  Cooper               : 0.00
% 50.37/35.28  Total                : 34.52
% 50.37/35.28  Index Insertion      : 0.00
% 50.37/35.28  Index Deletion       : 0.00
% 50.37/35.28  Index Matching       : 0.00
% 50.37/35.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
