%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:43 EST 2020

% Result     : Theorem 15.10s
% Output     : CNFRefutation 15.17s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 410 expanded)
%              Number of leaves         :   35 ( 153 expanded)
%              Depth                    :   15
%              Number of atoms          :  234 (1033 expanded)
%              Number of equality atoms :  160 ( 691 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_78,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_134,negated_conjecture,(
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

tff(f_110,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_24,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [A_60,B_61] : ~ r2_hidden(A_60,k2_zfmisc_1(A_60,B_61)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_91])).

tff(c_34,plain,(
    ! [A_15,B_16,C_17] :
      ( k4_xboole_0(k2_tarski(A_15,B_16),C_17) = k2_tarski(A_15,B_16)
      | r2_hidden(B_16,C_17)
      | r2_hidden(A_15,C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_3'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,k1_tarski(B_14)) = A_13
      | r2_hidden(B_14,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34501,plain,(
    ! [A_26805,C_26806,B_26807] :
      ( ~ r2_hidden(A_26805,C_26806)
      | k4_xboole_0(k2_tarski(A_26805,B_26807),C_26806) != k2_tarski(A_26805,B_26807) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34507,plain,(
    ! [A_26808,B_26809,B_26810] :
      ( ~ r2_hidden(A_26808,k1_tarski(B_26809))
      | r2_hidden(B_26809,k2_tarski(A_26808,B_26810)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_34501])).

tff(c_40822,plain,(
    ! [B_30037,B_30038] :
      ( r2_hidden(B_30037,k2_tarski('#skF_3'(k1_tarski(B_30037)),B_30038))
      | k1_tarski(B_30037) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_34507])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40838,plain,(
    ! [B_30038,B_30037] :
      ( B_30038 = B_30037
      | '#skF_3'(k1_tarski(B_30037)) = B_30037
      | k1_tarski(B_30037) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40822,c_2])).

tff(c_40857,plain,(
    ! [B_30037] :
      ( k1_tarski(B_30037) = k1_xboole_0
      | '#skF_3'(k1_tarski(B_30037)) = B_30037 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_40838])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_4'(A_43),A_43)
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_17432,plain,(
    ! [A_13355,C_13356,B_13357] :
      ( ~ r2_hidden(A_13355,C_13356)
      | k4_xboole_0(k2_tarski(A_13355,B_13357),C_13356) != k2_tarski(A_13355,B_13357) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_17438,plain,(
    ! [A_13358,B_13359,B_13360] :
      ( ~ r2_hidden(A_13358,k1_tarski(B_13359))
      | r2_hidden(B_13359,k2_tarski(A_13358,B_13360)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_17432])).

tff(c_17449,plain,(
    ! [B_13367,B_13368] :
      ( r2_hidden(B_13367,k2_tarski('#skF_4'(k1_tarski(B_13367)),B_13368))
      | k1_tarski(B_13367) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_52,c_17438])).

tff(c_17459,plain,(
    ! [B_13368,B_13367] :
      ( B_13368 = B_13367
      | '#skF_4'(k1_tarski(B_13367)) = B_13367
      | k1_tarski(B_13367) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_17449,c_2])).

tff(c_17477,plain,(
    ! [B_13367] :
      ( k1_tarski(B_13367) = k1_xboole_0
      | '#skF_4'(k1_tarski(B_13367)) = B_13367 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_17459])).

tff(c_6734,plain,(
    ! [B_3460,C_3461,A_3462] :
      ( ~ r2_hidden(B_3460,C_3461)
      | k4_xboole_0(k2_tarski(A_3462,B_3460),C_3461) != k2_tarski(A_3462,B_3460) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6815,plain,(
    ! [B_3546,B_3547,A_3548] :
      ( ~ r2_hidden(B_3546,k1_tarski(B_3547))
      | r2_hidden(B_3547,k2_tarski(A_3548,B_3546)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6734])).

tff(c_6824,plain,(
    ! [B_3549,A_3550] :
      ( r2_hidden(B_3549,k2_tarski(A_3550,'#skF_3'(k1_tarski(B_3549))))
      | k1_tarski(B_3549) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_6815])).

tff(c_6840,plain,(
    ! [B_3549,A_3550] :
      ( '#skF_3'(k1_tarski(B_3549)) = B_3549
      | B_3549 = A_3550
      | k1_tarski(B_3549) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6824,c_2])).

tff(c_6858,plain,(
    ! [B_3549] :
      ( k1_tarski(B_3549) = k1_xboole_0
      | '#skF_3'(k1_tarski(B_3549)) = B_3549 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6840])).

tff(c_58,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8'
    | k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8'
    | k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_199,plain,(
    k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_16676,plain,(
    ! [A_11553,B_11554,C_11555,D_11556] :
      ( k3_mcart_1(k5_mcart_1(A_11553,B_11554,C_11555,D_11556),k6_mcart_1(A_11553,B_11554,C_11555,D_11556),k7_mcart_1(A_11553,B_11554,C_11555,D_11556)) = D_11556
      | ~ m1_subset_1(D_11556,k3_zfmisc_1(A_11553,B_11554,C_11555))
      | k1_xboole_0 = C_11555
      | k1_xboole_0 = B_11554
      | k1_xboole_0 = A_11553 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16693,plain,
    ( k3_mcart_1('#skF_8',k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_16676])).

tff(c_16697,plain,
    ( k3_mcart_1('#skF_8',k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_16693])).

tff(c_16698,plain,(
    k3_mcart_1('#skF_8',k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_64,c_62,c_16697])).

tff(c_14636,plain,(
    ! [B_7277] :
      ( k1_tarski(B_7277) = k1_xboole_0
      | '#skF_3'(k1_tarski(B_7277)) = B_7277 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6840])).

tff(c_16699,plain,(
    ! [B_11633] :
      ( r2_hidden(B_11633,k1_tarski(B_11633))
      | k1_tarski(B_11633) = k1_xboole_0
      | k1_tarski(B_11633) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14636,c_44])).

tff(c_48,plain,(
    ! [C_35,A_24,D_36,E_37] :
      ( ~ r2_hidden(C_35,A_24)
      | k3_mcart_1(C_35,D_36,E_37) != '#skF_3'(A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16774,plain,(
    ! [B_12021,D_12022,E_12023] :
      ( k3_mcart_1(B_12021,D_12022,E_12023) != '#skF_3'(k1_tarski(B_12021))
      | k1_tarski(B_12021) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16699,c_48])).

tff(c_16777,plain,
    ( '#skF_3'(k1_tarski('#skF_8')) != '#skF_8'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16698,c_16774])).

tff(c_16846,plain,(
    '#skF_3'(k1_tarski('#skF_8')) != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_16777])).

tff(c_16852,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6858,c_16846])).

tff(c_30,plain,(
    ! [B_14,A_13] :
      ( ~ r2_hidden(B_14,A_13)
      | k4_xboole_0(A_13,k1_tarski(B_14)) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16955,plain,(
    ! [A_12560] :
      ( ~ r2_hidden('#skF_8',A_12560)
      | k4_xboole_0(A_12560,k1_xboole_0) != A_12560 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16852,c_30])).

tff(c_17075,plain,(
    ! [B_12793] : k4_xboole_0(k2_tarski('#skF_8',B_12793),k1_xboole_0) != k2_tarski('#skF_8',B_12793) ),
    inference(resolution,[status(thm)],[c_6,c_16955])).

tff(c_17091,plain,(
    ! [B_16] :
      ( r2_hidden(B_16,k1_xboole_0)
      | r2_hidden('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_17075])).

tff(c_17095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_94,c_17091])).

tff(c_17096,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16777])).

tff(c_17189,plain,(
    ! [A_13022] :
      ( ~ r2_hidden('#skF_8',A_13022)
      | k4_xboole_0(A_13022,k1_xboole_0) != A_13022 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17096,c_30])).

tff(c_17276,plain,(
    ! [B_13252] : k4_xboole_0(k2_tarski('#skF_8',B_13252),k1_xboole_0) != k2_tarski('#skF_8',B_13252) ),
    inference(resolution,[status(thm)],[c_6,c_17189])).

tff(c_17292,plain,(
    ! [B_16] :
      ( r2_hidden(B_16,k1_xboole_0)
      | r2_hidden('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_17276])).

tff(c_17296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_94,c_17292])).

tff(c_17297,plain,
    ( k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8'
    | k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_17345,plain,(
    k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_17297])).

tff(c_33676,plain,(
    ! [A_25232,B_25233,C_25234,D_25235] :
      ( k3_mcart_1(k5_mcart_1(A_25232,B_25233,C_25234,D_25235),k6_mcart_1(A_25232,B_25233,C_25234,D_25235),k7_mcart_1(A_25232,B_25233,C_25234,D_25235)) = D_25235
      | ~ m1_subset_1(D_25235,k3_zfmisc_1(A_25232,B_25233,C_25234))
      | k1_xboole_0 = C_25234
      | k1_xboole_0 = B_25233
      | k1_xboole_0 = A_25232 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_33702,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_17345,c_33676])).

tff(c_33706,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_33702])).

tff(c_33707,plain,(
    k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_64,c_62,c_33706])).

tff(c_40,plain,(
    ! [A_18,B_19,C_20] : k4_tarski(k4_tarski(A_18,B_19),C_20) = k3_mcart_1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_23669,plain,(
    ! [B_16365,B_16366] :
      ( r2_hidden(B_16365,k2_tarski('#skF_3'(k1_tarski(B_16365)),B_16366))
      | k1_tarski(B_16365) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_17438])).

tff(c_23685,plain,(
    ! [B_16366,B_16365] :
      ( B_16366 = B_16365
      | '#skF_3'(k1_tarski(B_16365)) = B_16365
      | k1_tarski(B_16365) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_23669,c_2])).

tff(c_31468,plain,(
    ! [B_20093] :
      ( k1_tarski(B_20093) = k1_xboole_0
      | '#skF_3'(k1_tarski(B_20093)) = B_20093 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_23685])).

tff(c_33432,plain,(
    ! [B_24369] :
      ( r2_hidden(B_24369,k1_tarski(B_24369))
      | k1_tarski(B_24369) = k1_xboole_0
      | k1_tarski(B_24369) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31468,c_44])).

tff(c_54,plain,(
    ! [D_52,A_43,C_51] :
      ( ~ r2_hidden(D_52,A_43)
      | k4_tarski(C_51,D_52) != '#skF_4'(A_43)
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_33468,plain,(
    ! [C_24524,B_24525] :
      ( k4_tarski(C_24524,B_24525) != '#skF_4'(k1_tarski(B_24525))
      | k1_tarski(B_24525) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_33432,c_54])).

tff(c_33480,plain,(
    ! [A_18,B_19,C_20] :
      ( k3_mcart_1(A_18,B_19,C_20) != '#skF_4'(k1_tarski(C_20))
      | k1_tarski(C_20) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_33468])).

tff(c_33879,plain,
    ( '#skF_4'(k1_tarski('#skF_8')) != '#skF_8'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_33707,c_33480])).

tff(c_33895,plain,(
    '#skF_4'(k1_tarski('#skF_8')) != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_33879])).

tff(c_33901,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_17477,c_33895])).

tff(c_33966,plain,(
    ! [A_25853] :
      ( ~ r2_hidden('#skF_8',A_25853)
      | k4_xboole_0(A_25853,k1_xboole_0) != A_25853 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33901,c_30])).

tff(c_34112,plain,(
    ! [A_26163] : k4_xboole_0(k2_tarski(A_26163,'#skF_8'),k1_xboole_0) != k2_tarski(A_26163,'#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_33966])).

tff(c_34128,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_8',k1_xboole_0)
      | r2_hidden(A_15,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_34112])).

tff(c_34132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_94,c_34128])).

tff(c_34133,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_33879])).

tff(c_34231,plain,(
    ! [A_26392] :
      ( ~ r2_hidden('#skF_8',A_26392)
      | k4_xboole_0(A_26392,k1_xboole_0) != A_26392 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34133,c_30])).

tff(c_34377,plain,(
    ! [B_26702] : k4_xboole_0(k2_tarski('#skF_8',B_26702),k1_xboole_0) != k2_tarski('#skF_8',B_26702) ),
    inference(resolution,[status(thm)],[c_6,c_34231])).

tff(c_34393,plain,(
    ! [B_16] :
      ( r2_hidden(B_16,k1_xboole_0)
      | r2_hidden('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_34377])).

tff(c_34397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_94,c_34393])).

tff(c_34398,plain,(
    k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_17297])).

tff(c_50774,plain,(
    ! [A_38581,B_38582,C_38583,D_38584] :
      ( k3_mcart_1(k5_mcart_1(A_38581,B_38582,C_38583,D_38584),k6_mcart_1(A_38581,B_38582,C_38583,D_38584),k7_mcart_1(A_38581,B_38582,C_38583,D_38584)) = D_38584
      | ~ m1_subset_1(D_38584,k3_zfmisc_1(A_38581,B_38582,C_38583))
      | k1_xboole_0 = C_38583
      | k1_xboole_0 = B_38582
      | k1_xboole_0 = A_38581 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50791,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8',k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_34398,c_50774])).

tff(c_50795,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8',k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50791])).

tff(c_50796,plain,(
    k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8',k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_64,c_62,c_50795])).

tff(c_48681,plain,(
    ! [B_33920] :
      ( k1_tarski(B_33920) = k1_xboole_0
      | '#skF_3'(k1_tarski(B_33920)) = B_33920 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_40838])).

tff(c_50719,plain,(
    ! [B_38348] :
      ( r2_hidden(B_38348,k1_tarski(B_38348))
      | k1_tarski(B_38348) = k1_xboole_0
      | k1_tarski(B_38348) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48681,c_44])).

tff(c_46,plain,(
    ! [D_36,A_24,C_35,E_37] :
      ( ~ r2_hidden(D_36,A_24)
      | k3_mcart_1(C_35,D_36,E_37) != '#skF_3'(A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_50735,plain,(
    ! [C_35,B_38348,E_37] :
      ( k3_mcart_1(C_35,B_38348,E_37) != '#skF_3'(k1_tarski(B_38348))
      | k1_tarski(B_38348) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50719,c_46])).

tff(c_50832,plain,
    ( '#skF_3'(k1_tarski('#skF_8')) != '#skF_8'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50796,c_50735])).

tff(c_50845,plain,(
    '#skF_3'(k1_tarski('#skF_8')) != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_50832])).

tff(c_50851,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40857,c_50845])).

tff(c_50912,plain,(
    ! [A_39201] :
      ( ~ r2_hidden('#skF_8',A_39201)
      | k4_xboole_0(A_39201,k1_xboole_0) != A_39201 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50851,c_30])).

tff(c_51055,plain,(
    ! [A_39510] : k4_xboole_0(k2_tarski(A_39510,'#skF_8'),k1_xboole_0) != k2_tarski(A_39510,'#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_50912])).

tff(c_51071,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_8',k1_xboole_0)
      | r2_hidden(A_15,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_51055])).

tff(c_51075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_94,c_51071])).

tff(c_51076,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50832])).

tff(c_51169,plain,(
    ! [A_39739] :
      ( ~ r2_hidden('#skF_8',A_39739)
      | k4_xboole_0(A_39739,k1_xboole_0) != A_39739 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51076,c_30])).

tff(c_51312,plain,(
    ! [B_40048] : k4_xboole_0(k2_tarski('#skF_8',B_40048),k1_xboole_0) != k2_tarski('#skF_8',B_40048) ),
    inference(resolution,[status(thm)],[c_6,c_51169])).

tff(c_51328,plain,(
    ! [B_16] :
      ( r2_hidden(B_16,k1_xboole_0)
      | r2_hidden('#skF_8',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_51312])).

tff(c_51332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_94,c_51328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:14:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.10/6.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.17/6.33  
% 15.17/6.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.17/6.33  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 15.17/6.33  
% 15.17/6.33  %Foreground sorts:
% 15.17/6.33  
% 15.17/6.33  
% 15.17/6.33  %Background operators:
% 15.17/6.33  
% 15.17/6.33  
% 15.17/6.33  %Foreground operators:
% 15.17/6.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.17/6.33  tff('#skF_4', type, '#skF_4': $i > $i).
% 15.17/6.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.17/6.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.17/6.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.17/6.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.17/6.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.17/6.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.17/6.33  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 15.17/6.33  tff('#skF_7', type, '#skF_7': $i).
% 15.17/6.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.17/6.33  tff('#skF_5', type, '#skF_5': $i).
% 15.17/6.33  tff('#skF_6', type, '#skF_6': $i).
% 15.17/6.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.17/6.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.17/6.33  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 15.17/6.33  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 15.17/6.33  tff('#skF_8', type, '#skF_8': $i).
% 15.17/6.33  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 15.17/6.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.17/6.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.17/6.33  tff('#skF_3', type, '#skF_3': $i > $i).
% 15.17/6.33  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 15.17/6.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.17/6.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.17/6.33  
% 15.17/6.37  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.17/6.37  tff(f_45, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 15.17/6.37  tff(f_58, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 15.17/6.37  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 15.17/6.37  tff(f_78, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 15.17/6.37  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 15.17/6.37  tff(f_134, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 15.17/6.37  tff(f_110, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 15.17/6.37  tff(f_94, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 15.17/6.37  tff(f_60, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 15.17/6.37  tff(c_24, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.17/6.37  tff(c_91, plain, (![A_60, B_61]: (~r2_hidden(A_60, k2_zfmisc_1(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.17/6.37  tff(c_94, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_91])).
% 15.17/6.37  tff(c_34, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k2_tarski(A_15, B_16), C_17)=k2_tarski(A_15, B_16) | r2_hidden(B_16, C_17) | r2_hidden(A_15, C_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.17/6.37  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.17/6.37  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.17/6.37  tff(c_44, plain, (![A_24]: (r2_hidden('#skF_3'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_78])).
% 15.17/6.37  tff(c_32, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k1_tarski(B_14))=A_13 | r2_hidden(B_14, A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.17/6.37  tff(c_34501, plain, (![A_26805, C_26806, B_26807]: (~r2_hidden(A_26805, C_26806) | k4_xboole_0(k2_tarski(A_26805, B_26807), C_26806)!=k2_tarski(A_26805, B_26807))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.17/6.37  tff(c_34507, plain, (![A_26808, B_26809, B_26810]: (~r2_hidden(A_26808, k1_tarski(B_26809)) | r2_hidden(B_26809, k2_tarski(A_26808, B_26810)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_34501])).
% 15.17/6.37  tff(c_40822, plain, (![B_30037, B_30038]: (r2_hidden(B_30037, k2_tarski('#skF_3'(k1_tarski(B_30037)), B_30038)) | k1_tarski(B_30037)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_34507])).
% 15.17/6.37  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 15.17/6.37  tff(c_40838, plain, (![B_30038, B_30037]: (B_30038=B_30037 | '#skF_3'(k1_tarski(B_30037))=B_30037 | k1_tarski(B_30037)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40822, c_2])).
% 15.17/6.37  tff(c_40857, plain, (![B_30037]: (k1_tarski(B_30037)=k1_xboole_0 | '#skF_3'(k1_tarski(B_30037))=B_30037)), inference(factorization, [status(thm), theory('equality')], [c_40838])).
% 15.17/6.37  tff(c_66, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.17/6.37  tff(c_64, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.17/6.37  tff(c_62, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.17/6.37  tff(c_60, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.17/6.37  tff(c_52, plain, (![A_43]: (r2_hidden('#skF_4'(A_43), A_43) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.17/6.37  tff(c_17432, plain, (![A_13355, C_13356, B_13357]: (~r2_hidden(A_13355, C_13356) | k4_xboole_0(k2_tarski(A_13355, B_13357), C_13356)!=k2_tarski(A_13355, B_13357))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.17/6.37  tff(c_17438, plain, (![A_13358, B_13359, B_13360]: (~r2_hidden(A_13358, k1_tarski(B_13359)) | r2_hidden(B_13359, k2_tarski(A_13358, B_13360)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_17432])).
% 15.17/6.37  tff(c_17449, plain, (![B_13367, B_13368]: (r2_hidden(B_13367, k2_tarski('#skF_4'(k1_tarski(B_13367)), B_13368)) | k1_tarski(B_13367)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_17438])).
% 15.17/6.37  tff(c_17459, plain, (![B_13368, B_13367]: (B_13368=B_13367 | '#skF_4'(k1_tarski(B_13367))=B_13367 | k1_tarski(B_13367)=k1_xboole_0)), inference(resolution, [status(thm)], [c_17449, c_2])).
% 15.17/6.37  tff(c_17477, plain, (![B_13367]: (k1_tarski(B_13367)=k1_xboole_0 | '#skF_4'(k1_tarski(B_13367))=B_13367)), inference(factorization, [status(thm), theory('equality')], [c_17459])).
% 15.17/6.37  tff(c_6734, plain, (![B_3460, C_3461, A_3462]: (~r2_hidden(B_3460, C_3461) | k4_xboole_0(k2_tarski(A_3462, B_3460), C_3461)!=k2_tarski(A_3462, B_3460))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.17/6.37  tff(c_6815, plain, (![B_3546, B_3547, A_3548]: (~r2_hidden(B_3546, k1_tarski(B_3547)) | r2_hidden(B_3547, k2_tarski(A_3548, B_3546)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_6734])).
% 15.17/6.37  tff(c_6824, plain, (![B_3549, A_3550]: (r2_hidden(B_3549, k2_tarski(A_3550, '#skF_3'(k1_tarski(B_3549)))) | k1_tarski(B_3549)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_6815])).
% 15.17/6.37  tff(c_6840, plain, (![B_3549, A_3550]: ('#skF_3'(k1_tarski(B_3549))=B_3549 | B_3549=A_3550 | k1_tarski(B_3549)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6824, c_2])).
% 15.17/6.37  tff(c_6858, plain, (![B_3549]: (k1_tarski(B_3549)=k1_xboole_0 | '#skF_3'(k1_tarski(B_3549))=B_3549)), inference(factorization, [status(thm), theory('equality')], [c_6840])).
% 15.17/6.37  tff(c_58, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8' | k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8' | k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.17/6.37  tff(c_199, plain, (k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8'), inference(splitLeft, [status(thm)], [c_58])).
% 15.17/6.37  tff(c_16676, plain, (![A_11553, B_11554, C_11555, D_11556]: (k3_mcart_1(k5_mcart_1(A_11553, B_11554, C_11555, D_11556), k6_mcart_1(A_11553, B_11554, C_11555, D_11556), k7_mcart_1(A_11553, B_11554, C_11555, D_11556))=D_11556 | ~m1_subset_1(D_11556, k3_zfmisc_1(A_11553, B_11554, C_11555)) | k1_xboole_0=C_11555 | k1_xboole_0=B_11554 | k1_xboole_0=A_11553)), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.17/6.37  tff(c_16693, plain, (k3_mcart_1('#skF_8', k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')) | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_199, c_16676])).
% 15.17/6.37  tff(c_16697, plain, (k3_mcart_1('#skF_8', k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_16693])).
% 15.17/6.37  tff(c_16698, plain, (k3_mcart_1('#skF_8', k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_66, c_64, c_62, c_16697])).
% 15.17/6.37  tff(c_14636, plain, (![B_7277]: (k1_tarski(B_7277)=k1_xboole_0 | '#skF_3'(k1_tarski(B_7277))=B_7277)), inference(factorization, [status(thm), theory('equality')], [c_6840])).
% 15.17/6.37  tff(c_16699, plain, (![B_11633]: (r2_hidden(B_11633, k1_tarski(B_11633)) | k1_tarski(B_11633)=k1_xboole_0 | k1_tarski(B_11633)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14636, c_44])).
% 15.17/6.37  tff(c_48, plain, (![C_35, A_24, D_36, E_37]: (~r2_hidden(C_35, A_24) | k3_mcart_1(C_35, D_36, E_37)!='#skF_3'(A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_78])).
% 15.17/6.37  tff(c_16774, plain, (![B_12021, D_12022, E_12023]: (k3_mcart_1(B_12021, D_12022, E_12023)!='#skF_3'(k1_tarski(B_12021)) | k1_tarski(B_12021)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16699, c_48])).
% 15.17/6.37  tff(c_16777, plain, ('#skF_3'(k1_tarski('#skF_8'))!='#skF_8' | k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_16698, c_16774])).
% 15.17/6.37  tff(c_16846, plain, ('#skF_3'(k1_tarski('#skF_8'))!='#skF_8'), inference(splitLeft, [status(thm)], [c_16777])).
% 15.17/6.37  tff(c_16852, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6858, c_16846])).
% 15.17/6.37  tff(c_30, plain, (![B_14, A_13]: (~r2_hidden(B_14, A_13) | k4_xboole_0(A_13, k1_tarski(B_14))!=A_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.17/6.37  tff(c_16955, plain, (![A_12560]: (~r2_hidden('#skF_8', A_12560) | k4_xboole_0(A_12560, k1_xboole_0)!=A_12560)), inference(superposition, [status(thm), theory('equality')], [c_16852, c_30])).
% 15.17/6.37  tff(c_17075, plain, (![B_12793]: (k4_xboole_0(k2_tarski('#skF_8', B_12793), k1_xboole_0)!=k2_tarski('#skF_8', B_12793))), inference(resolution, [status(thm)], [c_6, c_16955])).
% 15.17/6.37  tff(c_17091, plain, (![B_16]: (r2_hidden(B_16, k1_xboole_0) | r2_hidden('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_17075])).
% 15.17/6.37  tff(c_17095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_94, c_17091])).
% 15.17/6.37  tff(c_17096, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_16777])).
% 15.17/6.37  tff(c_17189, plain, (![A_13022]: (~r2_hidden('#skF_8', A_13022) | k4_xboole_0(A_13022, k1_xboole_0)!=A_13022)), inference(superposition, [status(thm), theory('equality')], [c_17096, c_30])).
% 15.17/6.37  tff(c_17276, plain, (![B_13252]: (k4_xboole_0(k2_tarski('#skF_8', B_13252), k1_xboole_0)!=k2_tarski('#skF_8', B_13252))), inference(resolution, [status(thm)], [c_6, c_17189])).
% 15.17/6.37  tff(c_17292, plain, (![B_16]: (r2_hidden(B_16, k1_xboole_0) | r2_hidden('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_17276])).
% 15.17/6.37  tff(c_17296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_94, c_17292])).
% 15.17/6.37  tff(c_17297, plain, (k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8' | k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_58])).
% 15.17/6.37  tff(c_17345, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8'), inference(splitLeft, [status(thm)], [c_17297])).
% 15.17/6.37  tff(c_33676, plain, (![A_25232, B_25233, C_25234, D_25235]: (k3_mcart_1(k5_mcart_1(A_25232, B_25233, C_25234, D_25235), k6_mcart_1(A_25232, B_25233, C_25234, D_25235), k7_mcart_1(A_25232, B_25233, C_25234, D_25235))=D_25235 | ~m1_subset_1(D_25235, k3_zfmisc_1(A_25232, B_25233, C_25234)) | k1_xboole_0=C_25234 | k1_xboole_0=B_25233 | k1_xboole_0=A_25232)), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.17/6.37  tff(c_33702, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')) | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_17345, c_33676])).
% 15.17/6.37  tff(c_33706, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_33702])).
% 15.17/6.37  tff(c_33707, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_66, c_64, c_62, c_33706])).
% 15.17/6.37  tff(c_40, plain, (![A_18, B_19, C_20]: (k4_tarski(k4_tarski(A_18, B_19), C_20)=k3_mcart_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.17/6.37  tff(c_23669, plain, (![B_16365, B_16366]: (r2_hidden(B_16365, k2_tarski('#skF_3'(k1_tarski(B_16365)), B_16366)) | k1_tarski(B_16365)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_17438])).
% 15.17/6.37  tff(c_23685, plain, (![B_16366, B_16365]: (B_16366=B_16365 | '#skF_3'(k1_tarski(B_16365))=B_16365 | k1_tarski(B_16365)=k1_xboole_0)), inference(resolution, [status(thm)], [c_23669, c_2])).
% 15.17/6.37  tff(c_31468, plain, (![B_20093]: (k1_tarski(B_20093)=k1_xboole_0 | '#skF_3'(k1_tarski(B_20093))=B_20093)), inference(factorization, [status(thm), theory('equality')], [c_23685])).
% 15.17/6.37  tff(c_33432, plain, (![B_24369]: (r2_hidden(B_24369, k1_tarski(B_24369)) | k1_tarski(B_24369)=k1_xboole_0 | k1_tarski(B_24369)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_31468, c_44])).
% 15.17/6.37  tff(c_54, plain, (![D_52, A_43, C_51]: (~r2_hidden(D_52, A_43) | k4_tarski(C_51, D_52)!='#skF_4'(A_43) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.17/6.37  tff(c_33468, plain, (![C_24524, B_24525]: (k4_tarski(C_24524, B_24525)!='#skF_4'(k1_tarski(B_24525)) | k1_tarski(B_24525)=k1_xboole_0)), inference(resolution, [status(thm)], [c_33432, c_54])).
% 15.17/6.37  tff(c_33480, plain, (![A_18, B_19, C_20]: (k3_mcart_1(A_18, B_19, C_20)!='#skF_4'(k1_tarski(C_20)) | k1_tarski(C_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_33468])).
% 15.17/6.37  tff(c_33879, plain, ('#skF_4'(k1_tarski('#skF_8'))!='#skF_8' | k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_33707, c_33480])).
% 15.17/6.37  tff(c_33895, plain, ('#skF_4'(k1_tarski('#skF_8'))!='#skF_8'), inference(splitLeft, [status(thm)], [c_33879])).
% 15.17/6.37  tff(c_33901, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_17477, c_33895])).
% 15.17/6.37  tff(c_33966, plain, (![A_25853]: (~r2_hidden('#skF_8', A_25853) | k4_xboole_0(A_25853, k1_xboole_0)!=A_25853)), inference(superposition, [status(thm), theory('equality')], [c_33901, c_30])).
% 15.17/6.37  tff(c_34112, plain, (![A_26163]: (k4_xboole_0(k2_tarski(A_26163, '#skF_8'), k1_xboole_0)!=k2_tarski(A_26163, '#skF_8'))), inference(resolution, [status(thm)], [c_4, c_33966])).
% 15.17/6.37  tff(c_34128, plain, (![A_15]: (r2_hidden('#skF_8', k1_xboole_0) | r2_hidden(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_34112])).
% 15.17/6.37  tff(c_34132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_94, c_34128])).
% 15.17/6.37  tff(c_34133, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_33879])).
% 15.17/6.37  tff(c_34231, plain, (![A_26392]: (~r2_hidden('#skF_8', A_26392) | k4_xboole_0(A_26392, k1_xboole_0)!=A_26392)), inference(superposition, [status(thm), theory('equality')], [c_34133, c_30])).
% 15.17/6.37  tff(c_34377, plain, (![B_26702]: (k4_xboole_0(k2_tarski('#skF_8', B_26702), k1_xboole_0)!=k2_tarski('#skF_8', B_26702))), inference(resolution, [status(thm)], [c_6, c_34231])).
% 15.17/6.37  tff(c_34393, plain, (![B_16]: (r2_hidden(B_16, k1_xboole_0) | r2_hidden('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_34377])).
% 15.17/6.37  tff(c_34397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_94, c_34393])).
% 15.17/6.37  tff(c_34398, plain, (k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_17297])).
% 15.17/6.37  tff(c_50774, plain, (![A_38581, B_38582, C_38583, D_38584]: (k3_mcart_1(k5_mcart_1(A_38581, B_38582, C_38583, D_38584), k6_mcart_1(A_38581, B_38582, C_38583, D_38584), k7_mcart_1(A_38581, B_38582, C_38583, D_38584))=D_38584 | ~m1_subset_1(D_38584, k3_zfmisc_1(A_38581, B_38582, C_38583)) | k1_xboole_0=C_38583 | k1_xboole_0=B_38582 | k1_xboole_0=A_38581)), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.17/6.37  tff(c_50791, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8', k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')) | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_34398, c_50774])).
% 15.17/6.37  tff(c_50795, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8', k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50791])).
% 15.17/6.37  tff(c_50796, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8', k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_66, c_64, c_62, c_50795])).
% 15.17/6.37  tff(c_48681, plain, (![B_33920]: (k1_tarski(B_33920)=k1_xboole_0 | '#skF_3'(k1_tarski(B_33920))=B_33920)), inference(factorization, [status(thm), theory('equality')], [c_40838])).
% 15.17/6.37  tff(c_50719, plain, (![B_38348]: (r2_hidden(B_38348, k1_tarski(B_38348)) | k1_tarski(B_38348)=k1_xboole_0 | k1_tarski(B_38348)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48681, c_44])).
% 15.17/6.37  tff(c_46, plain, (![D_36, A_24, C_35, E_37]: (~r2_hidden(D_36, A_24) | k3_mcart_1(C_35, D_36, E_37)!='#skF_3'(A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_78])).
% 15.17/6.37  tff(c_50735, plain, (![C_35, B_38348, E_37]: (k3_mcart_1(C_35, B_38348, E_37)!='#skF_3'(k1_tarski(B_38348)) | k1_tarski(B_38348)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50719, c_46])).
% 15.17/6.37  tff(c_50832, plain, ('#skF_3'(k1_tarski('#skF_8'))!='#skF_8' | k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_50796, c_50735])).
% 15.17/6.37  tff(c_50845, plain, ('#skF_3'(k1_tarski('#skF_8'))!='#skF_8'), inference(splitLeft, [status(thm)], [c_50832])).
% 15.17/6.37  tff(c_50851, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_40857, c_50845])).
% 15.17/6.37  tff(c_50912, plain, (![A_39201]: (~r2_hidden('#skF_8', A_39201) | k4_xboole_0(A_39201, k1_xboole_0)!=A_39201)), inference(superposition, [status(thm), theory('equality')], [c_50851, c_30])).
% 15.17/6.37  tff(c_51055, plain, (![A_39510]: (k4_xboole_0(k2_tarski(A_39510, '#skF_8'), k1_xboole_0)!=k2_tarski(A_39510, '#skF_8'))), inference(resolution, [status(thm)], [c_4, c_50912])).
% 15.17/6.37  tff(c_51071, plain, (![A_15]: (r2_hidden('#skF_8', k1_xboole_0) | r2_hidden(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_51055])).
% 15.17/6.37  tff(c_51075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_94, c_51071])).
% 15.17/6.37  tff(c_51076, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50832])).
% 15.17/6.37  tff(c_51169, plain, (![A_39739]: (~r2_hidden('#skF_8', A_39739) | k4_xboole_0(A_39739, k1_xboole_0)!=A_39739)), inference(superposition, [status(thm), theory('equality')], [c_51076, c_30])).
% 15.17/6.37  tff(c_51312, plain, (![B_40048]: (k4_xboole_0(k2_tarski('#skF_8', B_40048), k1_xboole_0)!=k2_tarski('#skF_8', B_40048))), inference(resolution, [status(thm)], [c_6, c_51169])).
% 15.17/6.37  tff(c_51328, plain, (![B_16]: (r2_hidden(B_16, k1_xboole_0) | r2_hidden('#skF_8', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_51312])).
% 15.17/6.37  tff(c_51332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_94, c_51328])).
% 15.17/6.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.17/6.37  
% 15.17/6.37  Inference rules
% 15.17/6.37  ----------------------
% 15.17/6.37  #Ref     : 0
% 15.17/6.37  #Sup     : 7313
% 15.17/6.37  #Fact    : 24
% 15.17/6.37  #Define  : 0
% 15.17/6.37  #Split   : 5
% 15.17/6.37  #Chain   : 0
% 15.17/6.37  #Close   : 0
% 15.17/6.37  
% 15.17/6.37  Ordering : KBO
% 15.17/6.37  
% 15.17/6.37  Simplification rules
% 15.17/6.37  ----------------------
% 15.17/6.37  #Subsume      : 2904
% 15.17/6.37  #Demod        : 2679
% 15.17/6.37  #Tautology    : 329
% 15.17/6.37  #SimpNegUnit  : 165
% 15.17/6.37  #BackRed      : 3
% 15.17/6.37  
% 15.17/6.37  #Partial instantiations: 20840
% 15.17/6.37  #Strategies tried      : 1
% 15.17/6.37  
% 15.17/6.37  Timing (in seconds)
% 15.17/6.37  ----------------------
% 15.17/6.38  Preprocessing        : 0.54
% 15.17/6.38  Parsing              : 0.27
% 15.17/6.38  CNF conversion       : 0.04
% 15.17/6.38  Main loop            : 4.86
% 15.17/6.38  Inferencing          : 2.13
% 15.17/6.38  Reduction            : 1.35
% 15.17/6.38  Demodulation         : 0.89
% 15.17/6.38  BG Simplification    : 0.24
% 15.17/6.38  Subsumption          : 0.82
% 15.17/6.38  Abstraction          : 0.34
% 15.17/6.38  MUC search           : 0.00
% 15.17/6.38  Cooper               : 0.00
% 15.17/6.38  Total                : 5.46
% 15.17/6.38  Index Insertion      : 0.00
% 15.17/6.38  Index Deletion       : 0.00
% 15.17/6.38  Index Matching       : 0.00
% 15.17/6.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
