%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:43 EST 2020

% Result     : Theorem 14.67s
% Output     : CNFRefutation 14.67s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 403 expanded)
%              Number of leaves         :   38 ( 151 expanded)
%              Depth                    :   11
%              Number of atoms          :  243 (1066 expanded)
%              Number of equality atoms :  157 ( 708 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_130,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_90,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_154,negated_conjecture,(
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

tff(f_126,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_26,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_158,plain,(
    ! [A_80,C_81,B_82] :
      ( r2_hidden(k2_mcart_1(A_80),C_81)
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_82,C_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_165,plain,(
    ! [A_80,B_10] :
      ( r2_hidden(k2_mcart_1(A_80),B_10)
      | ~ r2_hidden(A_80,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_158])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,k1_tarski(B_12)) = A_11
      | r2_hidden(B_12,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64621,plain,(
    ! [B_44910,C_44911,A_44912] :
      ( ~ r2_hidden(B_44910,C_44911)
      | k4_xboole_0(k2_tarski(A_44912,B_44910),C_44911) != k2_tarski(A_44912,B_44910) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64627,plain,(
    ! [B_44913,B_44914,A_44915] :
      ( ~ r2_hidden(B_44913,k1_tarski(B_44914))
      | r2_hidden(B_44914,k2_tarski(A_44915,B_44913)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_64621])).

tff(c_64774,plain,(
    ! [B_44928,A_44929,A_44930] :
      ( r2_hidden(B_44928,k2_tarski(A_44929,k2_mcart_1(A_44930)))
      | ~ r2_hidden(A_44930,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_165,c_64627])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64791,plain,(
    ! [A_44931,B_44932,A_44933] :
      ( k2_mcart_1(A_44931) = B_44932
      | B_44932 = A_44933
      | ~ r2_hidden(A_44931,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_64774,c_2])).

tff(c_64830,plain,(
    ! [A_80,B_44932,A_44933] :
      ( k2_mcart_1(k2_mcart_1(A_80)) = B_44932
      | B_44932 = A_44933
      | ~ r2_hidden(A_80,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_165,c_64791])).

tff(c_83097,plain,(
    ! [A_53987,B_53988] :
      ( ~ r2_hidden(A_53987,k1_xboole_0)
      | k2_mcart_1(k2_mcart_1(A_53987)) = B_53988 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_64830])).

tff(c_66,plain,(
    ! [A_54,B_55] : k2_mcart_1(k4_tarski(A_54,B_55)) = B_55 ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    ! [B_28,C_29] : k2_mcart_1(k4_tarski(B_28,C_29)) != k4_tarski(B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_78,plain,(
    ! [B_28,C_29] : k4_tarski(B_28,C_29) != C_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_46])).

tff(c_85252,plain,(
    ! [A_53987,C_29] :
      ( k2_mcart_1(k2_mcart_1(A_53987)) != C_29
      | ~ r2_hidden(A_53987,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83097,c_78])).

tff(c_87580,plain,(
    ! [A_53987] : ~ r2_hidden(A_53987,k1_xboole_0) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_85252])).

tff(c_50,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_3'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_87932,plain,(
    ! [B_64751,A_64752] :
      ( r2_hidden(B_64751,k2_tarski(A_64752,'#skF_3'(k1_tarski(B_64751))))
      | k1_tarski(B_64751) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_64627])).

tff(c_88104,plain,(
    ! [B_64751,A_64752] :
      ( '#skF_3'(k1_tarski(B_64751)) = B_64751
      | B_64751 = A_64752
      | k1_tarski(B_64751) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_87932,c_2])).

tff(c_88124,plain,(
    ! [B_64751] :
      ( k1_tarski(B_64751) = k1_xboole_0
      | '#skF_3'(k1_tarski(B_64751)) = B_64751 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_88104])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_85493,plain,(
    ! [A_56992,B_56993,C_56994,D_56995] :
      ( k7_mcart_1(A_56992,B_56993,C_56994,D_56995) = k2_mcart_1(D_56995)
      | ~ m1_subset_1(D_56995,k3_zfmisc_1(A_56992,B_56993,C_56994))
      | k1_xboole_0 = C_56994
      | k1_xboole_0 = B_56993
      | k1_xboole_0 = A_56992 ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_85528,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_85493])).

tff(c_85534,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_85528])).

tff(c_41057,plain,(
    ! [A_27124,B_27125,C_27126] : k4_tarski(k4_tarski(A_27124,B_27125),C_27126) = k3_mcart_1(A_27124,B_27125,C_27126) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_41079,plain,(
    ! [A_27124,B_27125,C_27126] : k3_mcart_1(A_27124,B_27125,C_27126) != C_27126 ),
    inference(superposition,[status(thm),theory(equality)],[c_41057,c_78])).

tff(c_24,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_220,plain,(
    ! [A_96,B_97,C_98] :
      ( r2_hidden(k1_mcart_1(A_96),B_97)
      | ~ r2_hidden(A_96,k2_zfmisc_1(B_97,C_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_231,plain,(
    ! [A_96,A_9] :
      ( r2_hidden(k1_mcart_1(A_96),A_9)
      | ~ r2_hidden(A_96,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_220])).

tff(c_550,plain,(
    ! [A_155,C_156,B_157] :
      ( ~ r2_hidden(A_155,C_156)
      | k4_xboole_0(k2_tarski(A_155,B_157),C_156) != k2_tarski(A_155,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_556,plain,(
    ! [A_158,B_159,B_160] :
      ( ~ r2_hidden(A_158,k1_tarski(B_159))
      | r2_hidden(B_159,k2_tarski(A_158,B_160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_550])).

tff(c_615,plain,(
    ! [B_164,A_165,B_166] :
      ( r2_hidden(B_164,k2_tarski(k1_mcart_1(A_165),B_166))
      | ~ r2_hidden(A_165,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_231,c_556])).

tff(c_632,plain,(
    ! [B_168,B_167,A_169] :
      ( B_168 = B_167
      | k1_mcart_1(A_169) = B_168
      | ~ r2_hidden(A_169,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_615,c_2])).

tff(c_659,plain,(
    ! [B_168,B_167,A_80] :
      ( B_168 = B_167
      | k1_mcart_1(k2_mcart_1(A_80)) = B_168
      | ~ r2_hidden(A_80,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_165,c_632])).

tff(c_19616,plain,(
    ! [A_9310,B_9311] :
      ( ~ r2_hidden(A_9310,k1_xboole_0)
      | k1_mcart_1(k2_mcart_1(A_9310)) = B_9311 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_659])).

tff(c_21668,plain,(
    ! [A_9310,C_29] :
      ( k1_mcart_1(k2_mcart_1(A_9310)) != C_29
      | ~ r2_hidden(A_9310,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19616,c_78])).

tff(c_23973,plain,(
    ! [A_9310] : ~ r2_hidden(A_9310,k1_xboole_0) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_21668])).

tff(c_24381,plain,(
    ! [B_20349,B_20350] :
      ( r2_hidden(B_20349,k2_tarski('#skF_3'(k1_tarski(B_20349)),B_20350))
      | k1_tarski(B_20349) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_556])).

tff(c_24553,plain,(
    ! [B_20350,B_20349] :
      ( B_20350 = B_20349
      | '#skF_3'(k1_tarski(B_20349)) = B_20349
      | k1_tarski(B_20349) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24381,c_2])).

tff(c_24573,plain,(
    ! [B_20349] :
      ( k1_tarski(B_20349) = k1_xboole_0
      | '#skF_3'(k1_tarski(B_20349)) = B_20349 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_24553])).

tff(c_1302,plain,(
    ! [A_236,B_237,C_238,D_239] :
      ( k7_mcart_1(A_236,B_237,C_238,D_239) = k2_mcart_1(D_239)
      | ~ m1_subset_1(D_239,k3_zfmisc_1(A_236,B_237,C_238))
      | k1_xboole_0 = C_238
      | k1_xboole_0 = B_237
      | k1_xboole_0 = A_236 ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1314,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_1302])).

tff(c_1320,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_1314])).

tff(c_68,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_171,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_24110,plain,(
    ! [A_19472,B_19473,C_19474,D_19475] :
      ( k3_mcart_1(k5_mcart_1(A_19472,B_19473,C_19474,D_19475),k6_mcart_1(A_19472,B_19473,C_19474,D_19475),k7_mcart_1(A_19472,B_19473,C_19474,D_19475)) = D_19475
      | ~ m1_subset_1(D_19475,k3_zfmisc_1(A_19472,B_19473,C_19474))
      | k1_xboole_0 = C_19474
      | k1_xboole_0 = B_19473
      | k1_xboole_0 = A_19472 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24142,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_24110])).

tff(c_24149,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1320,c_24142])).

tff(c_24150,plain,(
    k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_24149])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_761,plain,(
    ! [A_185,B_186,C_187] :
      ( k4_xboole_0(k2_tarski(A_185,B_186),C_187) = k2_tarski(A_185,B_186)
      | r2_hidden(B_186,C_187)
      | r2_hidden(A_185,C_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [B_12,A_11] :
      ( ~ r2_hidden(B_12,A_11)
      | k4_xboole_0(A_11,k1_tarski(B_12)) != A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40375,plain,(
    ! [B_26466,A_26467,B_26468] :
      ( ~ r2_hidden(B_26466,k2_tarski(A_26467,B_26468))
      | r2_hidden(B_26468,k1_tarski(B_26466))
      | r2_hidden(A_26467,k1_tarski(B_26466)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_28])).

tff(c_40408,plain,(
    ! [B_2,D_6] :
      ( r2_hidden(B_2,k1_tarski(D_6))
      | r2_hidden(D_6,k1_tarski(D_6)) ) ),
    inference(resolution,[status(thm)],[c_6,c_40375])).

tff(c_40471,plain,(
    ! [B_26627] : r2_hidden(B_26627,k1_tarski(B_26627)) ),
    inference(factorization,[status(thm),theory(equality)],[c_40408])).

tff(c_54,plain,(
    ! [C_41,A_30,D_42,E_43] :
      ( ~ r2_hidden(C_41,A_30)
      | k3_mcart_1(C_41,D_42,E_43) != '#skF_3'(A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40492,plain,(
    ! [B_26706,D_26707,E_26708] :
      ( k3_mcart_1(B_26706,D_26707,E_26708) != '#skF_3'(k1_tarski(B_26706))
      | k1_tarski(B_26706) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40471,c_54])).

tff(c_40501,plain,
    ( '#skF_3'(k1_tarski('#skF_7')) != '#skF_7'
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24150,c_40492])).

tff(c_40894,plain,(
    '#skF_3'(k1_tarski('#skF_7')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_40501])).

tff(c_40900,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24573,c_40894])).

tff(c_40422,plain,(
    ! [B_2] : r2_hidden(B_2,k1_tarski(B_2)) ),
    inference(factorization,[status(thm),theory(equality)],[c_40408])).

tff(c_40908,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40900,c_40422])).

tff(c_40932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23973,c_40908])).

tff(c_40933,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40501])).

tff(c_40941,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40933,c_40422])).

tff(c_40965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23973,c_40941])).

tff(c_40966,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_41026,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_40966])).

tff(c_64123,plain,(
    ! [A_44754,B_44755,C_44756,D_44757] :
      ( k3_mcart_1(k5_mcart_1(A_44754,B_44755,C_44756,D_44757),k6_mcart_1(A_44754,B_44755,C_44756,D_44757),k7_mcart_1(A_44754,B_44755,C_44756,D_44757)) = D_44757
      | ~ m1_subset_1(D_44757,k3_zfmisc_1(A_44754,B_44755,C_44756))
      | k1_xboole_0 = C_44756
      | k1_xboole_0 = B_44755
      | k1_xboole_0 = A_44754 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_64152,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_41026,c_64123])).

tff(c_64156,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64152])).

tff(c_64158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_41079,c_64156])).

tff(c_64159,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_40966])).

tff(c_87747,plain,(
    ! [A_64114,B_64115,C_64116,D_64117] :
      ( k3_mcart_1(k5_mcart_1(A_64114,B_64115,C_64116,D_64117),k6_mcart_1(A_64114,B_64115,C_64116,D_64117),k7_mcart_1(A_64114,B_64115,C_64116,D_64117)) = D_64117
      | ~ m1_subset_1(D_64117,k3_zfmisc_1(A_64114,B_64115,C_64116))
      | k1_xboole_0 = C_64116
      | k1_xboole_0 = B_64115
      | k1_xboole_0 = A_64114 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_87779,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_64159,c_87747])).

tff(c_87786,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_85534,c_87779])).

tff(c_87787,plain,(
    k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_72,c_87786])).

tff(c_64867,plain,(
    ! [A_44940,B_44941,C_44942] :
      ( k4_xboole_0(k2_tarski(A_44940,B_44941),C_44942) = k2_tarski(A_44940,B_44941)
      | r2_hidden(B_44941,C_44942)
      | r2_hidden(A_44940,C_44942) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_103331,plain,(
    ! [B_70952,A_70953,B_70954] :
      ( ~ r2_hidden(B_70952,k2_tarski(A_70953,B_70954))
      | r2_hidden(B_70954,k1_tarski(B_70952))
      | r2_hidden(A_70953,k1_tarski(B_70952)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64867,c_28])).

tff(c_103364,plain,(
    ! [B_2,D_6] :
      ( r2_hidden(B_2,k1_tarski(D_6))
      | r2_hidden(D_6,k1_tarski(D_6)) ) ),
    inference(resolution,[status(thm)],[c_6,c_103331])).

tff(c_103427,plain,(
    ! [B_71113] : r2_hidden(B_71113,k1_tarski(B_71113)) ),
    inference(factorization,[status(thm),theory(equality)],[c_103364])).

tff(c_52,plain,(
    ! [D_42,A_30,C_41,E_43] :
      ( ~ r2_hidden(D_42,A_30)
      | k3_mcart_1(C_41,D_42,E_43) != '#skF_3'(A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_103448,plain,(
    ! [C_71192,B_71193,E_71194] :
      ( k3_mcart_1(C_71192,B_71193,E_71194) != '#skF_3'(k1_tarski(B_71193))
      | k1_tarski(B_71193) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_103427,c_52])).

tff(c_103457,plain,
    ( '#skF_3'(k1_tarski('#skF_7')) != '#skF_7'
    | k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_87787,c_103448])).

tff(c_104670,plain,(
    '#skF_3'(k1_tarski('#skF_7')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_103457])).

tff(c_104677,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_88124,c_104670])).

tff(c_103378,plain,(
    ! [B_2] : r2_hidden(B_2,k1_tarski(B_2)) ),
    inference(factorization,[status(thm),theory(equality)],[c_103364])).

tff(c_104685,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_104677,c_103378])).

tff(c_104709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87580,c_104685])).

tff(c_104710,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_103457])).

tff(c_104718,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_104710,c_103378])).

tff(c_104742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87580,c_104718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:00:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.67/6.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.67/6.39  
% 14.67/6.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.67/6.39  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 14.67/6.39  
% 14.67/6.39  %Foreground sorts:
% 14.67/6.39  
% 14.67/6.39  
% 14.67/6.39  %Background operators:
% 14.67/6.39  
% 14.67/6.39  
% 14.67/6.39  %Foreground operators:
% 14.67/6.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.67/6.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.67/6.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.67/6.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.67/6.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.67/6.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.67/6.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.67/6.39  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 14.67/6.39  tff('#skF_7', type, '#skF_7': $i).
% 14.67/6.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.67/6.39  tff('#skF_5', type, '#skF_5': $i).
% 14.67/6.39  tff('#skF_6', type, '#skF_6': $i).
% 14.67/6.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.67/6.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.67/6.39  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 14.67/6.39  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 14.67/6.39  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 14.67/6.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.67/6.39  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 14.67/6.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.67/6.39  tff('#skF_4', type, '#skF_4': $i).
% 14.67/6.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 14.67/6.39  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 14.67/6.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.67/6.39  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 14.67/6.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.67/6.39  
% 14.67/6.41  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.67/6.41  tff(f_65, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 14.67/6.41  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 14.67/6.41  tff(f_55, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 14.67/6.41  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 14.67/6.41  tff(f_130, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 14.67/6.41  tff(f_74, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 14.67/6.41  tff(f_90, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 14.67/6.41  tff(f_154, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 14.67/6.41  tff(f_126, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 14.67/6.41  tff(f_57, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 14.67/6.41  tff(f_106, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 14.67/6.41  tff(c_26, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.67/6.41  tff(c_158, plain, (![A_80, C_81, B_82]: (r2_hidden(k2_mcart_1(A_80), C_81) | ~r2_hidden(A_80, k2_zfmisc_1(B_82, C_81)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.67/6.41  tff(c_165, plain, (![A_80, B_10]: (r2_hidden(k2_mcart_1(A_80), B_10) | ~r2_hidden(A_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_158])).
% 14.67/6.41  tff(c_30, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k1_tarski(B_12))=A_11 | r2_hidden(B_12, A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.67/6.41  tff(c_64621, plain, (![B_44910, C_44911, A_44912]: (~r2_hidden(B_44910, C_44911) | k4_xboole_0(k2_tarski(A_44912, B_44910), C_44911)!=k2_tarski(A_44912, B_44910))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.67/6.41  tff(c_64627, plain, (![B_44913, B_44914, A_44915]: (~r2_hidden(B_44913, k1_tarski(B_44914)) | r2_hidden(B_44914, k2_tarski(A_44915, B_44913)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_64621])).
% 14.67/6.41  tff(c_64774, plain, (![B_44928, A_44929, A_44930]: (r2_hidden(B_44928, k2_tarski(A_44929, k2_mcart_1(A_44930))) | ~r2_hidden(A_44930, k1_xboole_0))), inference(resolution, [status(thm)], [c_165, c_64627])).
% 14.67/6.41  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.67/6.41  tff(c_64791, plain, (![A_44931, B_44932, A_44933]: (k2_mcart_1(A_44931)=B_44932 | B_44932=A_44933 | ~r2_hidden(A_44931, k1_xboole_0))), inference(resolution, [status(thm)], [c_64774, c_2])).
% 14.67/6.41  tff(c_64830, plain, (![A_80, B_44932, A_44933]: (k2_mcart_1(k2_mcart_1(A_80))=B_44932 | B_44932=A_44933 | ~r2_hidden(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_165, c_64791])).
% 14.67/6.41  tff(c_83097, plain, (![A_53987, B_53988]: (~r2_hidden(A_53987, k1_xboole_0) | k2_mcart_1(k2_mcart_1(A_53987))=B_53988)), inference(factorization, [status(thm), theory('equality')], [c_64830])).
% 14.67/6.41  tff(c_66, plain, (![A_54, B_55]: (k2_mcart_1(k4_tarski(A_54, B_55))=B_55)), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.67/6.41  tff(c_46, plain, (![B_28, C_29]: (k2_mcart_1(k4_tarski(B_28, C_29))!=k4_tarski(B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.67/6.41  tff(c_78, plain, (![B_28, C_29]: (k4_tarski(B_28, C_29)!=C_29)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_46])).
% 14.67/6.41  tff(c_85252, plain, (![A_53987, C_29]: (k2_mcart_1(k2_mcart_1(A_53987))!=C_29 | ~r2_hidden(A_53987, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_83097, c_78])).
% 14.67/6.41  tff(c_87580, plain, (![A_53987]: (~r2_hidden(A_53987, k1_xboole_0))), inference(reflexivity, [status(thm), theory('equality')], [c_85252])).
% 14.67/6.41  tff(c_50, plain, (![A_30]: (r2_hidden('#skF_3'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.67/6.41  tff(c_87932, plain, (![B_64751, A_64752]: (r2_hidden(B_64751, k2_tarski(A_64752, '#skF_3'(k1_tarski(B_64751)))) | k1_tarski(B_64751)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_64627])).
% 14.67/6.41  tff(c_88104, plain, (![B_64751, A_64752]: ('#skF_3'(k1_tarski(B_64751))=B_64751 | B_64751=A_64752 | k1_tarski(B_64751)=k1_xboole_0)), inference(resolution, [status(thm)], [c_87932, c_2])).
% 14.67/6.41  tff(c_88124, plain, (![B_64751]: (k1_tarski(B_64751)=k1_xboole_0 | '#skF_3'(k1_tarski(B_64751))=B_64751)), inference(factorization, [status(thm), theory('equality')], [c_88104])).
% 14.67/6.41  tff(c_76, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_154])).
% 14.67/6.41  tff(c_74, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_154])).
% 14.67/6.41  tff(c_72, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_154])).
% 14.67/6.41  tff(c_70, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 14.67/6.41  tff(c_85493, plain, (![A_56992, B_56993, C_56994, D_56995]: (k7_mcart_1(A_56992, B_56993, C_56994, D_56995)=k2_mcart_1(D_56995) | ~m1_subset_1(D_56995, k3_zfmisc_1(A_56992, B_56993, C_56994)) | k1_xboole_0=C_56994 | k1_xboole_0=B_56993 | k1_xboole_0=A_56992)), inference(cnfTransformation, [status(thm)], [f_126])).
% 14.67/6.41  tff(c_85528, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_70, c_85493])).
% 14.67/6.41  tff(c_85534, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_76, c_74, c_72, c_85528])).
% 14.67/6.41  tff(c_41057, plain, (![A_27124, B_27125, C_27126]: (k4_tarski(k4_tarski(A_27124, B_27125), C_27126)=k3_mcart_1(A_27124, B_27125, C_27126))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.67/6.41  tff(c_41079, plain, (![A_27124, B_27125, C_27126]: (k3_mcart_1(A_27124, B_27125, C_27126)!=C_27126)), inference(superposition, [status(thm), theory('equality')], [c_41057, c_78])).
% 14.67/6.41  tff(c_24, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 14.67/6.41  tff(c_220, plain, (![A_96, B_97, C_98]: (r2_hidden(k1_mcart_1(A_96), B_97) | ~r2_hidden(A_96, k2_zfmisc_1(B_97, C_98)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.67/6.41  tff(c_231, plain, (![A_96, A_9]: (r2_hidden(k1_mcart_1(A_96), A_9) | ~r2_hidden(A_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_220])).
% 14.67/6.41  tff(c_550, plain, (![A_155, C_156, B_157]: (~r2_hidden(A_155, C_156) | k4_xboole_0(k2_tarski(A_155, B_157), C_156)!=k2_tarski(A_155, B_157))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.67/6.41  tff(c_556, plain, (![A_158, B_159, B_160]: (~r2_hidden(A_158, k1_tarski(B_159)) | r2_hidden(B_159, k2_tarski(A_158, B_160)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_550])).
% 14.67/6.41  tff(c_615, plain, (![B_164, A_165, B_166]: (r2_hidden(B_164, k2_tarski(k1_mcart_1(A_165), B_166)) | ~r2_hidden(A_165, k1_xboole_0))), inference(resolution, [status(thm)], [c_231, c_556])).
% 14.67/6.41  tff(c_632, plain, (![B_168, B_167, A_169]: (B_168=B_167 | k1_mcart_1(A_169)=B_168 | ~r2_hidden(A_169, k1_xboole_0))), inference(resolution, [status(thm)], [c_615, c_2])).
% 14.67/6.41  tff(c_659, plain, (![B_168, B_167, A_80]: (B_168=B_167 | k1_mcart_1(k2_mcart_1(A_80))=B_168 | ~r2_hidden(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_165, c_632])).
% 14.67/6.41  tff(c_19616, plain, (![A_9310, B_9311]: (~r2_hidden(A_9310, k1_xboole_0) | k1_mcart_1(k2_mcart_1(A_9310))=B_9311)), inference(factorization, [status(thm), theory('equality')], [c_659])).
% 14.67/6.41  tff(c_21668, plain, (![A_9310, C_29]: (k1_mcart_1(k2_mcart_1(A_9310))!=C_29 | ~r2_hidden(A_9310, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_19616, c_78])).
% 14.67/6.41  tff(c_23973, plain, (![A_9310]: (~r2_hidden(A_9310, k1_xboole_0))), inference(reflexivity, [status(thm), theory('equality')], [c_21668])).
% 14.67/6.41  tff(c_24381, plain, (![B_20349, B_20350]: (r2_hidden(B_20349, k2_tarski('#skF_3'(k1_tarski(B_20349)), B_20350)) | k1_tarski(B_20349)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_556])).
% 14.67/6.41  tff(c_24553, plain, (![B_20350, B_20349]: (B_20350=B_20349 | '#skF_3'(k1_tarski(B_20349))=B_20349 | k1_tarski(B_20349)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24381, c_2])).
% 14.67/6.41  tff(c_24573, plain, (![B_20349]: (k1_tarski(B_20349)=k1_xboole_0 | '#skF_3'(k1_tarski(B_20349))=B_20349)), inference(factorization, [status(thm), theory('equality')], [c_24553])).
% 14.67/6.41  tff(c_1302, plain, (![A_236, B_237, C_238, D_239]: (k7_mcart_1(A_236, B_237, C_238, D_239)=k2_mcart_1(D_239) | ~m1_subset_1(D_239, k3_zfmisc_1(A_236, B_237, C_238)) | k1_xboole_0=C_238 | k1_xboole_0=B_237 | k1_xboole_0=A_236)), inference(cnfTransformation, [status(thm)], [f_126])).
% 14.67/6.41  tff(c_1314, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_70, c_1302])).
% 14.67/6.41  tff(c_1320, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_76, c_74, c_72, c_1314])).
% 14.67/6.41  tff(c_68, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_154])).
% 14.67/6.41  tff(c_171, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_68])).
% 14.67/6.41  tff(c_24110, plain, (![A_19472, B_19473, C_19474, D_19475]: (k3_mcart_1(k5_mcart_1(A_19472, B_19473, C_19474, D_19475), k6_mcart_1(A_19472, B_19473, C_19474, D_19475), k7_mcart_1(A_19472, B_19473, C_19474, D_19475))=D_19475 | ~m1_subset_1(D_19475, k3_zfmisc_1(A_19472, B_19473, C_19474)) | k1_xboole_0=C_19474 | k1_xboole_0=B_19473 | k1_xboole_0=A_19472)), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.67/6.41  tff(c_24142, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_171, c_24110])).
% 14.67/6.41  tff(c_24149, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1320, c_24142])).
% 14.67/6.41  tff(c_24150, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_76, c_74, c_72, c_24149])).
% 14.67/6.41  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 14.67/6.41  tff(c_761, plain, (![A_185, B_186, C_187]: (k4_xboole_0(k2_tarski(A_185, B_186), C_187)=k2_tarski(A_185, B_186) | r2_hidden(B_186, C_187) | r2_hidden(A_185, C_187))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.67/6.41  tff(c_28, plain, (![B_12, A_11]: (~r2_hidden(B_12, A_11) | k4_xboole_0(A_11, k1_tarski(B_12))!=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.67/6.41  tff(c_40375, plain, (![B_26466, A_26467, B_26468]: (~r2_hidden(B_26466, k2_tarski(A_26467, B_26468)) | r2_hidden(B_26468, k1_tarski(B_26466)) | r2_hidden(A_26467, k1_tarski(B_26466)))), inference(superposition, [status(thm), theory('equality')], [c_761, c_28])).
% 14.67/6.41  tff(c_40408, plain, (![B_2, D_6]: (r2_hidden(B_2, k1_tarski(D_6)) | r2_hidden(D_6, k1_tarski(D_6)))), inference(resolution, [status(thm)], [c_6, c_40375])).
% 14.67/6.41  tff(c_40471, plain, (![B_26627]: (r2_hidden(B_26627, k1_tarski(B_26627)))), inference(factorization, [status(thm), theory('equality')], [c_40408])).
% 14.67/6.41  tff(c_54, plain, (![C_41, A_30, D_42, E_43]: (~r2_hidden(C_41, A_30) | k3_mcart_1(C_41, D_42, E_43)!='#skF_3'(A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.67/6.41  tff(c_40492, plain, (![B_26706, D_26707, E_26708]: (k3_mcart_1(B_26706, D_26707, E_26708)!='#skF_3'(k1_tarski(B_26706)) | k1_tarski(B_26706)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40471, c_54])).
% 14.67/6.41  tff(c_40501, plain, ('#skF_3'(k1_tarski('#skF_7'))!='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24150, c_40492])).
% 14.67/6.41  tff(c_40894, plain, ('#skF_3'(k1_tarski('#skF_7'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_40501])).
% 14.67/6.41  tff(c_40900, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24573, c_40894])).
% 14.67/6.41  tff(c_40422, plain, (![B_2]: (r2_hidden(B_2, k1_tarski(B_2)))), inference(factorization, [status(thm), theory('equality')], [c_40408])).
% 14.67/6.41  tff(c_40908, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40900, c_40422])).
% 14.67/6.41  tff(c_40932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23973, c_40908])).
% 14.67/6.41  tff(c_40933, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40501])).
% 14.67/6.41  tff(c_40941, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40933, c_40422])).
% 14.67/6.41  tff(c_40965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23973, c_40941])).
% 14.67/6.41  tff(c_40966, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_68])).
% 14.67/6.41  tff(c_41026, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_40966])).
% 14.67/6.41  tff(c_64123, plain, (![A_44754, B_44755, C_44756, D_44757]: (k3_mcart_1(k5_mcart_1(A_44754, B_44755, C_44756, D_44757), k6_mcart_1(A_44754, B_44755, C_44756, D_44757), k7_mcart_1(A_44754, B_44755, C_44756, D_44757))=D_44757 | ~m1_subset_1(D_44757, k3_zfmisc_1(A_44754, B_44755, C_44756)) | k1_xboole_0=C_44756 | k1_xboole_0=B_44755 | k1_xboole_0=A_44754)), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.67/6.41  tff(c_64152, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_41026, c_64123])).
% 14.67/6.41  tff(c_64156, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64152])).
% 14.67/6.41  tff(c_64158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_74, c_72, c_41079, c_64156])).
% 14.67/6.41  tff(c_64159, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_40966])).
% 14.67/6.41  tff(c_87747, plain, (![A_64114, B_64115, C_64116, D_64117]: (k3_mcart_1(k5_mcart_1(A_64114, B_64115, C_64116, D_64117), k6_mcart_1(A_64114, B_64115, C_64116, D_64117), k7_mcart_1(A_64114, B_64115, C_64116, D_64117))=D_64117 | ~m1_subset_1(D_64117, k3_zfmisc_1(A_64114, B_64115, C_64116)) | k1_xboole_0=C_64116 | k1_xboole_0=B_64115 | k1_xboole_0=A_64114)), inference(cnfTransformation, [status(thm)], [f_106])).
% 14.67/6.41  tff(c_87779, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_64159, c_87747])).
% 14.67/6.41  tff(c_87786, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_85534, c_87779])).
% 14.67/6.41  tff(c_87787, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k2_mcart_1('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_76, c_74, c_72, c_87786])).
% 14.67/6.41  tff(c_64867, plain, (![A_44940, B_44941, C_44942]: (k4_xboole_0(k2_tarski(A_44940, B_44941), C_44942)=k2_tarski(A_44940, B_44941) | r2_hidden(B_44941, C_44942) | r2_hidden(A_44940, C_44942))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.67/6.41  tff(c_103331, plain, (![B_70952, A_70953, B_70954]: (~r2_hidden(B_70952, k2_tarski(A_70953, B_70954)) | r2_hidden(B_70954, k1_tarski(B_70952)) | r2_hidden(A_70953, k1_tarski(B_70952)))), inference(superposition, [status(thm), theory('equality')], [c_64867, c_28])).
% 14.67/6.41  tff(c_103364, plain, (![B_2, D_6]: (r2_hidden(B_2, k1_tarski(D_6)) | r2_hidden(D_6, k1_tarski(D_6)))), inference(resolution, [status(thm)], [c_6, c_103331])).
% 14.67/6.41  tff(c_103427, plain, (![B_71113]: (r2_hidden(B_71113, k1_tarski(B_71113)))), inference(factorization, [status(thm), theory('equality')], [c_103364])).
% 14.67/6.41  tff(c_52, plain, (![D_42, A_30, C_41, E_43]: (~r2_hidden(D_42, A_30) | k3_mcart_1(C_41, D_42, E_43)!='#skF_3'(A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.67/6.41  tff(c_103448, plain, (![C_71192, B_71193, E_71194]: (k3_mcart_1(C_71192, B_71193, E_71194)!='#skF_3'(k1_tarski(B_71193)) | k1_tarski(B_71193)=k1_xboole_0)), inference(resolution, [status(thm)], [c_103427, c_52])).
% 14.67/6.41  tff(c_103457, plain, ('#skF_3'(k1_tarski('#skF_7'))!='#skF_7' | k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_87787, c_103448])).
% 14.67/6.41  tff(c_104670, plain, ('#skF_3'(k1_tarski('#skF_7'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_103457])).
% 14.67/6.41  tff(c_104677, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_88124, c_104670])).
% 14.67/6.41  tff(c_103378, plain, (![B_2]: (r2_hidden(B_2, k1_tarski(B_2)))), inference(factorization, [status(thm), theory('equality')], [c_103364])).
% 14.67/6.41  tff(c_104685, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104677, c_103378])).
% 14.67/6.41  tff(c_104709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87580, c_104685])).
% 14.67/6.41  tff(c_104710, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_103457])).
% 14.67/6.41  tff(c_104718, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104710, c_103378])).
% 14.67/6.41  tff(c_104742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87580, c_104718])).
% 14.67/6.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.67/6.41  
% 14.67/6.41  Inference rules
% 14.67/6.41  ----------------------
% 14.67/6.41  #Ref     : 3
% 14.67/6.41  #Sup     : 17026
% 14.67/6.41  #Fact    : 40
% 14.67/6.41  #Define  : 0
% 14.67/6.41  #Split   : 7
% 14.67/6.41  #Chain   : 0
% 14.67/6.41  #Close   : 0
% 14.67/6.41  
% 14.67/6.42  Ordering : KBO
% 14.67/6.42  
% 14.67/6.42  Simplification rules
% 14.67/6.42  ----------------------
% 14.67/6.42  #Subsume      : 4549
% 14.67/6.42  #Demod        : 3096
% 14.67/6.42  #Tautology    : 334
% 14.67/6.42  #SimpNegUnit  : 126
% 14.67/6.42  #BackRed      : 3
% 14.67/6.42  
% 14.67/6.42  #Partial instantiations: 39858
% 14.67/6.42  #Strategies tried      : 1
% 14.67/6.42  
% 14.67/6.42  Timing (in seconds)
% 14.67/6.42  ----------------------
% 14.67/6.42  Preprocessing        : 0.34
% 14.67/6.42  Parsing              : 0.17
% 14.67/6.42  CNF conversion       : 0.03
% 14.67/6.42  Main loop            : 5.28
% 14.67/6.42  Inferencing          : 1.80
% 14.67/6.42  Reduction            : 1.46
% 14.67/6.42  Demodulation         : 0.99
% 14.67/6.42  BG Simplification    : 0.27
% 14.67/6.42  Subsumption          : 1.33
% 14.67/6.42  Abstraction          : 0.29
% 14.67/6.42  MUC search           : 0.00
% 14.67/6.42  Cooper               : 0.00
% 14.67/6.42  Total                : 5.67
% 14.67/6.42  Index Insertion      : 0.00
% 14.67/6.42  Index Deletion       : 0.00
% 14.67/6.42  Index Matching       : 0.00
% 14.67/6.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
