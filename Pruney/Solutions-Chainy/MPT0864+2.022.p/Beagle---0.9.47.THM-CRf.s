%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:11 EST 2020

% Result     : Theorem 6.03s
% Output     : CNFRefutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 437 expanded)
%              Number of leaves         :   41 ( 159 expanded)
%              Depth                    :   14
%              Number of atoms          :  175 ( 861 expanded)
%              Number of equality atoms :   91 ( 441 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_8 > #skF_10 > #skF_2 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_111,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_76,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_94,plain,(
    k4_tarski('#skF_11','#skF_12') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3210,plain,(
    ! [A_9185,B_9186] : k2_mcart_1(k4_tarski(A_9185,B_9186)) = B_9186 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3219,plain,(
    k2_mcart_1('#skF_10') = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_3210])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1625,plain,(
    ! [A_1778,B_1779,C_1780] :
      ( ~ r2_hidden('#skF_2'(A_1778,B_1779,C_1780),B_1779)
      | r2_hidden('#skF_3'(A_1778,B_1779,C_1780),C_1780)
      | k4_xboole_0(A_1778,B_1779) = C_1780 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2227,plain,(
    ! [A_4483,C_4484] :
      ( r2_hidden('#skF_3'(A_4483,A_4483,C_4484),C_4484)
      | k4_xboole_0(A_4483,A_4483) = C_4484 ) ),
    inference(resolution,[status(thm)],[c_24,c_1625])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_26] : k2_zfmisc_1(A_26,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_390,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_mcart_1(A_115) = B_116
      | ~ r2_hidden(A_115,k2_zfmisc_1(k1_tarski(B_116),C_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_404,plain,(
    ! [A_118,B_119] :
      ( k1_mcart_1(A_118) = B_119
      | ~ r2_hidden(A_118,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_390])).

tff(c_459,plain,(
    ! [B_120] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_120)) = '#skF_12'
      | r1_tarski(k1_xboole_0,B_120) ) ),
    inference(resolution,[status(thm)],[c_6,c_404])).

tff(c_411,plain,(
    ! [B_2,B_119] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_2)) = B_119
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_404])).

tff(c_462,plain,(
    ! [B_119,B_120] :
      ( B_119 = '#skF_12'
      | r1_tarski(k1_xboole_0,B_120)
      | r1_tarski(k1_xboole_0,B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_411])).

tff(c_811,plain,(
    ! [B_120] :
      ( r1_tarski(k1_xboole_0,B_120)
      | r1_tarski(k1_xboole_0,B_120) ) ),
    inference(splitLeft,[status(thm)],[c_462])).

tff(c_848,plain,(
    ! [B_120] : r1_tarski(k1_xboole_0,B_120) ),
    inference(factorization,[status(thm),theory(equality)],[c_811])).

tff(c_921,plain,(
    ! [A_1726,C_1727,B_1728] :
      ( r2_hidden(k2_mcart_1(A_1726),C_1727)
      | ~ r2_hidden(A_1726,k2_zfmisc_1(k1_tarski(B_1728),C_1727)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_936,plain,(
    ! [A_1729] :
      ( r2_hidden(k2_mcart_1(A_1729),k1_xboole_0)
      | ~ r2_hidden(A_1729,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_921])).

tff(c_76,plain,(
    ! [B_35,A_34] :
      ( ~ r1_tarski(B_35,A_34)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_947,plain,(
    ! [A_1729] :
      ( ~ r1_tarski(k1_xboole_0,k2_mcart_1(A_1729))
      | ~ r2_hidden(A_1729,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_936,c_76])).

tff(c_964,plain,(
    ! [A_1729] : ~ r2_hidden(A_1729,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_947])).

tff(c_2266,plain,(
    ! [A_4483] : k4_xboole_0(A_4483,A_4483) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2227,c_964])).

tff(c_66,plain,(
    ! [B_29] : k4_xboole_0(k1_tarski(B_29),k1_tarski(B_29)) != k1_tarski(B_29) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2278,plain,(
    ! [B_29] : k1_tarski(B_29) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2266,c_66])).

tff(c_86,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_9'(A_41),A_41)
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_195,plain,(
    ! [C_67,A_68] :
      ( C_67 = A_68
      | ~ r2_hidden(C_67,k1_tarski(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_203,plain,(
    ! [A_68] :
      ( '#skF_9'(k1_tarski(A_68)) = A_68
      | k1_tarski(A_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_86,c_195])).

tff(c_3036,plain,(
    ! [A_68] : '#skF_9'(k1_tarski(A_68)) = A_68 ),
    inference(negUnitSimplification,[status(thm)],[c_2278,c_203])).

tff(c_3040,plain,(
    ! [A_7395] : '#skF_9'(k1_tarski(A_7395)) = A_7395 ),
    inference(negUnitSimplification,[status(thm)],[c_2278,c_203])).

tff(c_875,plain,(
    ! [C_1716,A_1717,D_1718] :
      ( ~ r2_hidden(C_1716,A_1717)
      | k4_tarski(C_1716,D_1718) != '#skF_9'(A_1717)
      | k1_xboole_0 = A_1717 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_887,plain,(
    ! [A_41,D_1718] :
      ( k4_tarski('#skF_9'(A_41),D_1718) != '#skF_9'(A_41)
      | k1_xboole_0 = A_41 ) ),
    inference(resolution,[status(thm)],[c_86,c_875])).

tff(c_3058,plain,(
    ! [A_7395,D_1718] :
      ( k4_tarski(A_7395,D_1718) != '#skF_9'(k1_tarski(A_7395))
      | k1_tarski(A_7395) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3040,c_887])).

tff(c_3078,plain,(
    ! [A_7395,D_1718] :
      ( k4_tarski(A_7395,D_1718) != A_7395
      | k1_tarski(A_7395) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3036,c_3058])).

tff(c_3079,plain,(
    ! [A_7395,D_1718] : k4_tarski(A_7395,D_1718) != A_7395 ),
    inference(negUnitSimplification,[status(thm)],[c_2278,c_3078])).

tff(c_137,plain,(
    ! [A_60,B_61] : k1_mcart_1(k4_tarski(A_60,B_61)) = A_60 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_146,plain,(
    k1_mcart_1('#skF_10') = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_137])).

tff(c_92,plain,
    ( k2_mcart_1('#skF_10') = '#skF_10'
    | k1_mcart_1('#skF_10') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_153,plain,
    ( k2_mcart_1('#skF_10') = '#skF_10'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_92])).

tff(c_154,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_156,plain,(
    k4_tarski('#skF_10','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_94])).

tff(c_3091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3079,c_156])).

tff(c_3093,plain,(
    ! [B_7608] : B_7608 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_462])).

tff(c_70,plain,(
    ! [A_30] : m1_subset_1('#skF_8'(A_30),A_30) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_244,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(A_82,B_83)
      | ~ m1_subset_1(A_82,k1_zfmisc_1(B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_253,plain,(
    ! [B_83] : r1_tarski('#skF_8'(k1_zfmisc_1(B_83)),B_83) ),
    inference(resolution,[status(thm)],[c_70,c_244])).

tff(c_3133,plain,(
    ! [B_83] : r1_tarski('#skF_12',B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_3093,c_253])).

tff(c_42,plain,(
    ! [D_22,B_18] : r2_hidden(D_22,k2_tarski(D_22,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_206,plain,(
    ! [B_69,A_70] :
      ( ~ r1_tarski(B_69,A_70)
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_220,plain,(
    ! [D_22,B_18] : ~ r1_tarski(k2_tarski(D_22,B_18),D_22) ),
    inference(resolution,[status(thm)],[c_42,c_206])).

tff(c_3143,plain,(
    ! [D_22] : ~ r1_tarski('#skF_12',D_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_3093,c_220])).

tff(c_3207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3133,c_3143])).

tff(c_3208,plain,(
    k2_mcart_1('#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_3226,plain,(
    '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3219,c_3208])).

tff(c_3209,plain,(
    '#skF_11' != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_3232,plain,(
    '#skF_11' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_3209])).

tff(c_5020,plain,(
    ! [A_12953,B_12954,C_12955] :
      ( r2_hidden('#skF_2'(A_12953,B_12954,C_12955),A_12953)
      | r2_hidden('#skF_3'(A_12953,B_12954,C_12955),C_12955)
      | k4_xboole_0(A_12953,B_12954) = C_12955 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6832,plain,(
    ! [A_18862,C_18863] :
      ( r2_hidden('#skF_3'(A_18862,A_18862,C_18863),C_18863)
      | k4_xboole_0(A_18862,A_18862) = C_18863 ) ),
    inference(resolution,[status(thm)],[c_5020,c_22])).

tff(c_3482,plain,(
    ! [A_9240,B_9241,C_9242] :
      ( k1_mcart_1(A_9240) = B_9241
      | ~ r2_hidden(A_9240,k2_zfmisc_1(k1_tarski(B_9241),C_9242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3496,plain,(
    ! [A_9243,B_9244] :
      ( k1_mcart_1(A_9243) = B_9244
      | ~ r2_hidden(A_9243,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_3482])).

tff(c_3516,plain,(
    ! [B_9245] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_9245)) = '#skF_11'
      | r1_tarski(k1_xboole_0,B_9245) ) ),
    inference(resolution,[status(thm)],[c_6,c_3496])).

tff(c_3503,plain,(
    ! [B_2,B_9244] :
      ( k1_mcart_1('#skF_1'(k1_xboole_0,B_2)) = B_9244
      | r1_tarski(k1_xboole_0,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_3496])).

tff(c_3519,plain,(
    ! [B_9244,B_9245] :
      ( B_9244 = '#skF_11'
      | r1_tarski(k1_xboole_0,B_9245)
      | r1_tarski(k1_xboole_0,B_9245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3516,c_3503])).

tff(c_4436,plain,(
    ! [B_9245] :
      ( r1_tarski(k1_xboole_0,B_9245)
      | r1_tarski(k1_xboole_0,B_9245) ) ),
    inference(splitLeft,[status(thm)],[c_3519])).

tff(c_4445,plain,(
    ! [B_9245] : r1_tarski(k1_xboole_0,B_9245) ),
    inference(factorization,[status(thm),theory(equality)],[c_4436])).

tff(c_3909,plain,(
    ! [A_10787,C_10788,B_10789] :
      ( r2_hidden(k2_mcart_1(A_10787),C_10788)
      | ~ r2_hidden(A_10787,k2_zfmisc_1(k1_tarski(B_10789),C_10788)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3928,plain,(
    ! [A_10825] :
      ( r2_hidden(k2_mcart_1(A_10825),k1_xboole_0)
      | ~ r2_hidden(A_10825,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_3909])).

tff(c_3946,plain,(
    ! [A_10825] :
      ( ~ r1_tarski(k1_xboole_0,k2_mcart_1(A_10825))
      | ~ r2_hidden(A_10825,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3928,c_76])).

tff(c_4460,plain,(
    ! [A_10825] : ~ r2_hidden(A_10825,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4445,c_3946])).

tff(c_6873,plain,(
    ! [A_18862] : k4_xboole_0(A_18862,A_18862) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6832,c_4460])).

tff(c_6884,plain,(
    ! [B_29] : k1_tarski(B_29) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6873,c_66])).

tff(c_3284,plain,(
    ! [A_9194] :
      ( r2_hidden('#skF_9'(A_9194),A_9194)
      | k1_xboole_0 = A_9194 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3293,plain,(
    ! [A_12] :
      ( '#skF_9'(k1_tarski(A_12)) = A_12
      | k1_tarski(A_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3284,c_26])).

tff(c_6983,plain,(
    ! [A_12] : '#skF_9'(k1_tarski(A_12)) = A_12 ),
    inference(negUnitSimplification,[status(thm)],[c_6884,c_3293])).

tff(c_6987,plain,(
    ! [A_19149] : '#skF_9'(k1_tarski(A_19149)) = A_19149 ),
    inference(negUnitSimplification,[status(thm)],[c_6884,c_3293])).

tff(c_4475,plain,(
    ! [D_12863,A_12864,C_12865] :
      ( ~ r2_hidden(D_12863,A_12864)
      | k4_tarski(C_12865,D_12863) != '#skF_9'(A_12864)
      | k1_xboole_0 = A_12864 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4491,plain,(
    ! [C_12865,A_41] :
      ( k4_tarski(C_12865,'#skF_9'(A_41)) != '#skF_9'(A_41)
      | k1_xboole_0 = A_41 ) ),
    inference(resolution,[status(thm)],[c_86,c_4475])).

tff(c_7005,plain,(
    ! [C_12865,A_19149] :
      ( k4_tarski(C_12865,A_19149) != '#skF_9'(k1_tarski(A_19149))
      | k1_tarski(A_19149) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6987,c_4491])).

tff(c_7025,plain,(
    ! [C_12865,A_19149] :
      ( k4_tarski(C_12865,A_19149) != A_19149
      | k1_tarski(A_19149) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6983,c_7005])).

tff(c_7026,plain,(
    ! [C_12865,A_19149] : k4_tarski(C_12865,A_19149) != A_19149 ),
    inference(negUnitSimplification,[status(thm)],[c_6884,c_7025])).

tff(c_3234,plain,(
    k4_tarski('#skF_11','#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_94])).

tff(c_7071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7026,c_3234])).

tff(c_7073,plain,(
    ! [B_19364] : B_19364 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_3519])).

tff(c_3231,plain,(
    k2_mcart_1('#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3226,c_3219])).

tff(c_7175,plain,(
    '#skF_11' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_7073,c_3231])).

tff(c_7216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3232,c_7175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.03/2.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.03/2.24  
% 6.03/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.03/2.24  %$ r2_hidden > r1_tarski > m1_subset_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_9 > #skF_11 > #skF_6 > #skF_8 > #skF_10 > #skF_2 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_12 > #skF_4
% 6.03/2.24  
% 6.03/2.24  %Foreground sorts:
% 6.03/2.24  
% 6.03/2.24  
% 6.03/2.24  %Background operators:
% 6.03/2.24  
% 6.03/2.24  
% 6.03/2.24  %Foreground operators:
% 6.03/2.24  tff('#skF_9', type, '#skF_9': $i > $i).
% 6.03/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.03/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.03/2.24  tff('#skF_11', type, '#skF_11': $i).
% 6.03/2.24  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 6.03/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.03/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.03/2.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.03/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.03/2.24  tff('#skF_8', type, '#skF_8': $i > $i).
% 6.03/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.03/2.24  tff('#skF_10', type, '#skF_10': $i).
% 6.03/2.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.03/2.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.03/2.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.03/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.03/2.24  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 6.03/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.03/2.24  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.03/2.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.03/2.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.03/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.03/2.24  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.03/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.03/2.24  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.03/2.24  tff('#skF_12', type, '#skF_12': $i).
% 6.03/2.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.03/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.03/2.24  
% 6.03/2.26  tff(f_121, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 6.03/2.26  tff(f_95, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 6.03/2.26  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.03/2.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.03/2.26  tff(f_68, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.03/2.26  tff(f_91, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 6.03/2.26  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.03/2.26  tff(f_73, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.03/2.26  tff(f_111, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 6.03/2.26  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 6.03/2.26  tff(f_76, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 6.03/2.26  tff(f_80, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.03/2.26  tff(f_58, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.03/2.26  tff(c_94, plain, (k4_tarski('#skF_11', '#skF_12')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.03/2.26  tff(c_3210, plain, (![A_9185, B_9186]: (k2_mcart_1(k4_tarski(A_9185, B_9186))=B_9186)), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.03/2.26  tff(c_3219, plain, (k2_mcart_1('#skF_10')='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_94, c_3210])).
% 6.03/2.26  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.03/2.26  tff(c_1625, plain, (![A_1778, B_1779, C_1780]: (~r2_hidden('#skF_2'(A_1778, B_1779, C_1780), B_1779) | r2_hidden('#skF_3'(A_1778, B_1779, C_1780), C_1780) | k4_xboole_0(A_1778, B_1779)=C_1780)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.03/2.26  tff(c_2227, plain, (![A_4483, C_4484]: (r2_hidden('#skF_3'(A_4483, A_4483, C_4484), C_4484) | k4_xboole_0(A_4483, A_4483)=C_4484)), inference(resolution, [status(thm)], [c_24, c_1625])).
% 6.03/2.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.03/2.26  tff(c_62, plain, (![A_26]: (k2_zfmisc_1(A_26, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.03/2.26  tff(c_390, plain, (![A_115, B_116, C_117]: (k1_mcart_1(A_115)=B_116 | ~r2_hidden(A_115, k2_zfmisc_1(k1_tarski(B_116), C_117)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.03/2.26  tff(c_404, plain, (![A_118, B_119]: (k1_mcart_1(A_118)=B_119 | ~r2_hidden(A_118, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_390])).
% 6.03/2.26  tff(c_459, plain, (![B_120]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_120))='#skF_12' | r1_tarski(k1_xboole_0, B_120))), inference(resolution, [status(thm)], [c_6, c_404])).
% 6.03/2.26  tff(c_411, plain, (![B_2, B_119]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_2))=B_119 | r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_404])).
% 6.03/2.26  tff(c_462, plain, (![B_119, B_120]: (B_119='#skF_12' | r1_tarski(k1_xboole_0, B_120) | r1_tarski(k1_xboole_0, B_120))), inference(superposition, [status(thm), theory('equality')], [c_459, c_411])).
% 6.03/2.26  tff(c_811, plain, (![B_120]: (r1_tarski(k1_xboole_0, B_120) | r1_tarski(k1_xboole_0, B_120))), inference(splitLeft, [status(thm)], [c_462])).
% 6.03/2.26  tff(c_848, plain, (![B_120]: (r1_tarski(k1_xboole_0, B_120))), inference(factorization, [status(thm), theory('equality')], [c_811])).
% 6.03/2.26  tff(c_921, plain, (![A_1726, C_1727, B_1728]: (r2_hidden(k2_mcart_1(A_1726), C_1727) | ~r2_hidden(A_1726, k2_zfmisc_1(k1_tarski(B_1728), C_1727)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.03/2.26  tff(c_936, plain, (![A_1729]: (r2_hidden(k2_mcart_1(A_1729), k1_xboole_0) | ~r2_hidden(A_1729, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_921])).
% 6.03/2.26  tff(c_76, plain, (![B_35, A_34]: (~r1_tarski(B_35, A_34) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.03/2.26  tff(c_947, plain, (![A_1729]: (~r1_tarski(k1_xboole_0, k2_mcart_1(A_1729)) | ~r2_hidden(A_1729, k1_xboole_0))), inference(resolution, [status(thm)], [c_936, c_76])).
% 6.03/2.26  tff(c_964, plain, (![A_1729]: (~r2_hidden(A_1729, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_848, c_947])).
% 6.03/2.26  tff(c_2266, plain, (![A_4483]: (k4_xboole_0(A_4483, A_4483)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2227, c_964])).
% 6.03/2.26  tff(c_66, plain, (![B_29]: (k4_xboole_0(k1_tarski(B_29), k1_tarski(B_29))!=k1_tarski(B_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.03/2.26  tff(c_2278, plain, (![B_29]: (k1_tarski(B_29)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2266, c_66])).
% 6.03/2.26  tff(c_86, plain, (![A_41]: (r2_hidden('#skF_9'(A_41), A_41) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.03/2.26  tff(c_195, plain, (![C_67, A_68]: (C_67=A_68 | ~r2_hidden(C_67, k1_tarski(A_68)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.03/2.26  tff(c_203, plain, (![A_68]: ('#skF_9'(k1_tarski(A_68))=A_68 | k1_tarski(A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_86, c_195])).
% 6.03/2.26  tff(c_3036, plain, (![A_68]: ('#skF_9'(k1_tarski(A_68))=A_68)), inference(negUnitSimplification, [status(thm)], [c_2278, c_203])).
% 6.03/2.26  tff(c_3040, plain, (![A_7395]: ('#skF_9'(k1_tarski(A_7395))=A_7395)), inference(negUnitSimplification, [status(thm)], [c_2278, c_203])).
% 6.03/2.26  tff(c_875, plain, (![C_1716, A_1717, D_1718]: (~r2_hidden(C_1716, A_1717) | k4_tarski(C_1716, D_1718)!='#skF_9'(A_1717) | k1_xboole_0=A_1717)), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.03/2.26  tff(c_887, plain, (![A_41, D_1718]: (k4_tarski('#skF_9'(A_41), D_1718)!='#skF_9'(A_41) | k1_xboole_0=A_41)), inference(resolution, [status(thm)], [c_86, c_875])).
% 6.03/2.26  tff(c_3058, plain, (![A_7395, D_1718]: (k4_tarski(A_7395, D_1718)!='#skF_9'(k1_tarski(A_7395)) | k1_tarski(A_7395)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3040, c_887])).
% 6.03/2.26  tff(c_3078, plain, (![A_7395, D_1718]: (k4_tarski(A_7395, D_1718)!=A_7395 | k1_tarski(A_7395)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3036, c_3058])).
% 6.03/2.26  tff(c_3079, plain, (![A_7395, D_1718]: (k4_tarski(A_7395, D_1718)!=A_7395)), inference(negUnitSimplification, [status(thm)], [c_2278, c_3078])).
% 6.03/2.26  tff(c_137, plain, (![A_60, B_61]: (k1_mcart_1(k4_tarski(A_60, B_61))=A_60)), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.03/2.26  tff(c_146, plain, (k1_mcart_1('#skF_10')='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_94, c_137])).
% 6.03/2.26  tff(c_92, plain, (k2_mcart_1('#skF_10')='#skF_10' | k1_mcart_1('#skF_10')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.03/2.26  tff(c_153, plain, (k2_mcart_1('#skF_10')='#skF_10' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_92])).
% 6.03/2.26  tff(c_154, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_153])).
% 6.03/2.26  tff(c_156, plain, (k4_tarski('#skF_10', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_94])).
% 6.03/2.26  tff(c_3091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3079, c_156])).
% 6.03/2.26  tff(c_3093, plain, (![B_7608]: (B_7608='#skF_12')), inference(splitRight, [status(thm)], [c_462])).
% 6.03/2.26  tff(c_70, plain, (![A_30]: (m1_subset_1('#skF_8'(A_30), A_30))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.03/2.26  tff(c_244, plain, (![A_82, B_83]: (r1_tarski(A_82, B_83) | ~m1_subset_1(A_82, k1_zfmisc_1(B_83)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.03/2.26  tff(c_253, plain, (![B_83]: (r1_tarski('#skF_8'(k1_zfmisc_1(B_83)), B_83))), inference(resolution, [status(thm)], [c_70, c_244])).
% 6.03/2.26  tff(c_3133, plain, (![B_83]: (r1_tarski('#skF_12', B_83))), inference(superposition, [status(thm), theory('equality')], [c_3093, c_253])).
% 6.03/2.26  tff(c_42, plain, (![D_22, B_18]: (r2_hidden(D_22, k2_tarski(D_22, B_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.03/2.26  tff(c_206, plain, (![B_69, A_70]: (~r1_tarski(B_69, A_70) | ~r2_hidden(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.03/2.26  tff(c_220, plain, (![D_22, B_18]: (~r1_tarski(k2_tarski(D_22, B_18), D_22))), inference(resolution, [status(thm)], [c_42, c_206])).
% 6.03/2.26  tff(c_3143, plain, (![D_22]: (~r1_tarski('#skF_12', D_22))), inference(superposition, [status(thm), theory('equality')], [c_3093, c_220])).
% 6.03/2.26  tff(c_3207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3133, c_3143])).
% 6.03/2.26  tff(c_3208, plain, (k2_mcart_1('#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_153])).
% 6.03/2.26  tff(c_3226, plain, ('#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3219, c_3208])).
% 6.03/2.26  tff(c_3209, plain, ('#skF_11'!='#skF_10'), inference(splitRight, [status(thm)], [c_153])).
% 6.03/2.26  tff(c_3232, plain, ('#skF_11'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_3209])).
% 6.03/2.26  tff(c_5020, plain, (![A_12953, B_12954, C_12955]: (r2_hidden('#skF_2'(A_12953, B_12954, C_12955), A_12953) | r2_hidden('#skF_3'(A_12953, B_12954, C_12955), C_12955) | k4_xboole_0(A_12953, B_12954)=C_12955)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.03/2.26  tff(c_22, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.03/2.26  tff(c_6832, plain, (![A_18862, C_18863]: (r2_hidden('#skF_3'(A_18862, A_18862, C_18863), C_18863) | k4_xboole_0(A_18862, A_18862)=C_18863)), inference(resolution, [status(thm)], [c_5020, c_22])).
% 6.03/2.26  tff(c_3482, plain, (![A_9240, B_9241, C_9242]: (k1_mcart_1(A_9240)=B_9241 | ~r2_hidden(A_9240, k2_zfmisc_1(k1_tarski(B_9241), C_9242)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.03/2.26  tff(c_3496, plain, (![A_9243, B_9244]: (k1_mcart_1(A_9243)=B_9244 | ~r2_hidden(A_9243, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_3482])).
% 6.03/2.26  tff(c_3516, plain, (![B_9245]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_9245))='#skF_11' | r1_tarski(k1_xboole_0, B_9245))), inference(resolution, [status(thm)], [c_6, c_3496])).
% 6.03/2.26  tff(c_3503, plain, (![B_2, B_9244]: (k1_mcart_1('#skF_1'(k1_xboole_0, B_2))=B_9244 | r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_3496])).
% 6.03/2.26  tff(c_3519, plain, (![B_9244, B_9245]: (B_9244='#skF_11' | r1_tarski(k1_xboole_0, B_9245) | r1_tarski(k1_xboole_0, B_9245))), inference(superposition, [status(thm), theory('equality')], [c_3516, c_3503])).
% 6.03/2.26  tff(c_4436, plain, (![B_9245]: (r1_tarski(k1_xboole_0, B_9245) | r1_tarski(k1_xboole_0, B_9245))), inference(splitLeft, [status(thm)], [c_3519])).
% 6.03/2.26  tff(c_4445, plain, (![B_9245]: (r1_tarski(k1_xboole_0, B_9245))), inference(factorization, [status(thm), theory('equality')], [c_4436])).
% 6.03/2.26  tff(c_3909, plain, (![A_10787, C_10788, B_10789]: (r2_hidden(k2_mcart_1(A_10787), C_10788) | ~r2_hidden(A_10787, k2_zfmisc_1(k1_tarski(B_10789), C_10788)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.03/2.26  tff(c_3928, plain, (![A_10825]: (r2_hidden(k2_mcart_1(A_10825), k1_xboole_0) | ~r2_hidden(A_10825, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_3909])).
% 6.03/2.26  tff(c_3946, plain, (![A_10825]: (~r1_tarski(k1_xboole_0, k2_mcart_1(A_10825)) | ~r2_hidden(A_10825, k1_xboole_0))), inference(resolution, [status(thm)], [c_3928, c_76])).
% 6.03/2.26  tff(c_4460, plain, (![A_10825]: (~r2_hidden(A_10825, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4445, c_3946])).
% 6.03/2.26  tff(c_6873, plain, (![A_18862]: (k4_xboole_0(A_18862, A_18862)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6832, c_4460])).
% 6.03/2.26  tff(c_6884, plain, (![B_29]: (k1_tarski(B_29)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6873, c_66])).
% 6.03/2.26  tff(c_3284, plain, (![A_9194]: (r2_hidden('#skF_9'(A_9194), A_9194) | k1_xboole_0=A_9194)), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.03/2.26  tff(c_26, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.03/2.26  tff(c_3293, plain, (![A_12]: ('#skF_9'(k1_tarski(A_12))=A_12 | k1_tarski(A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3284, c_26])).
% 6.03/2.26  tff(c_6983, plain, (![A_12]: ('#skF_9'(k1_tarski(A_12))=A_12)), inference(negUnitSimplification, [status(thm)], [c_6884, c_3293])).
% 6.03/2.26  tff(c_6987, plain, (![A_19149]: ('#skF_9'(k1_tarski(A_19149))=A_19149)), inference(negUnitSimplification, [status(thm)], [c_6884, c_3293])).
% 6.03/2.26  tff(c_4475, plain, (![D_12863, A_12864, C_12865]: (~r2_hidden(D_12863, A_12864) | k4_tarski(C_12865, D_12863)!='#skF_9'(A_12864) | k1_xboole_0=A_12864)), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.03/2.26  tff(c_4491, plain, (![C_12865, A_41]: (k4_tarski(C_12865, '#skF_9'(A_41))!='#skF_9'(A_41) | k1_xboole_0=A_41)), inference(resolution, [status(thm)], [c_86, c_4475])).
% 6.03/2.26  tff(c_7005, plain, (![C_12865, A_19149]: (k4_tarski(C_12865, A_19149)!='#skF_9'(k1_tarski(A_19149)) | k1_tarski(A_19149)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6987, c_4491])).
% 6.03/2.26  tff(c_7025, plain, (![C_12865, A_19149]: (k4_tarski(C_12865, A_19149)!=A_19149 | k1_tarski(A_19149)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6983, c_7005])).
% 6.03/2.26  tff(c_7026, plain, (![C_12865, A_19149]: (k4_tarski(C_12865, A_19149)!=A_19149)), inference(negUnitSimplification, [status(thm)], [c_6884, c_7025])).
% 6.03/2.26  tff(c_3234, plain, (k4_tarski('#skF_11', '#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_94])).
% 6.03/2.26  tff(c_7071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7026, c_3234])).
% 6.03/2.26  tff(c_7073, plain, (![B_19364]: (B_19364='#skF_11')), inference(splitRight, [status(thm)], [c_3519])).
% 6.03/2.26  tff(c_3231, plain, (k2_mcart_1('#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3226, c_3219])).
% 6.03/2.26  tff(c_7175, plain, ('#skF_11'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_7073, c_3231])).
% 6.03/2.26  tff(c_7216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3232, c_7175])).
% 6.03/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.03/2.26  
% 6.03/2.26  Inference rules
% 6.03/2.26  ----------------------
% 6.03/2.26  #Ref     : 0
% 6.03/2.26  #Sup     : 1231
% 6.03/2.26  #Fact    : 12
% 6.03/2.26  #Define  : 0
% 6.03/2.26  #Split   : 4
% 6.03/2.26  #Chain   : 0
% 6.03/2.26  #Close   : 0
% 6.03/2.26  
% 6.03/2.26  Ordering : KBO
% 6.03/2.26  
% 6.03/2.26  Simplification rules
% 6.03/2.26  ----------------------
% 6.03/2.26  #Subsume      : 185
% 6.03/2.26  #Demod        : 297
% 6.03/2.26  #Tautology    : 288
% 6.03/2.26  #SimpNegUnit  : 60
% 6.03/2.26  #BackRed      : 22
% 6.03/2.26  
% 6.03/2.26  #Partial instantiations: 11100
% 6.03/2.26  #Strategies tried      : 1
% 6.03/2.26  
% 6.03/2.26  Timing (in seconds)
% 6.03/2.26  ----------------------
% 6.03/2.26  Preprocessing        : 0.37
% 6.03/2.26  Parsing              : 0.18
% 6.03/2.26  CNF conversion       : 0.03
% 6.03/2.26  Main loop            : 1.04
% 6.03/2.26  Inferencing          : 0.50
% 6.03/2.26  Reduction            : 0.25
% 6.03/2.26  Demodulation         : 0.16
% 6.03/2.26  BG Simplification    : 0.05
% 6.03/2.26  Subsumption          : 0.16
% 6.03/2.26  Abstraction          : 0.05
% 6.03/2.26  MUC search           : 0.00
% 6.03/2.27  Cooper               : 0.00
% 6.03/2.27  Total                : 1.45
% 6.03/2.27  Index Insertion      : 0.00
% 6.03/2.27  Index Deletion       : 0.00
% 6.03/2.27  Index Matching       : 0.00
% 6.03/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
