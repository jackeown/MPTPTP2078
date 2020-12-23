%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:13 EST 2020

% Result     : Theorem 12.72s
% Output     : CNFRefutation 12.86s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 216 expanded)
%              Number of leaves         :   27 (  85 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 366 expanded)
%              Number of equality atoms :   60 ( 256 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_46,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_83,plain,(
    ! [A_37,B_38] : k2_mcart_1(k4_tarski(A_37,B_38)) = B_38 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_83])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_195,plain,(
    ! [A_53,C_54,B_55] :
      ( r2_hidden(k2_mcart_1(A_53),C_54)
      | ~ r2_hidden(A_53,k2_zfmisc_1(B_55,C_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_204,plain,(
    ! [A_56] :
      ( r2_hidden(k2_mcart_1(A_56),k1_xboole_0)
      | ~ r2_hidden(A_56,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_195])).

tff(c_207,plain,
    ( r2_hidden('#skF_6',k1_xboole_0)
    | ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_204])).

tff(c_211,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_99,plain,(
    ! [A_39,B_40] : k1_mcart_1(k4_tarski(A_39,B_40)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_108,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_99])).

tff(c_44,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_115,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_92,c_44])).

tff(c_116,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_118,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_46])).

tff(c_145,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_3'(A_43),A_43)
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_150,plain,(
    ! [A_1] :
      ( '#skF_3'(k1_tarski(A_1)) = A_1
      | k1_tarski(A_1) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_145,c_2])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2794,plain,(
    ! [C_3156,A_3157,D_3158] :
      ( ~ r2_hidden(C_3156,A_3157)
      | k4_tarski(C_3156,D_3158) != '#skF_3'(A_3157)
      | k1_xboole_0 = A_3157 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20697,plain,(
    ! [C_15717,D_15718] :
      ( k4_tarski(C_15717,D_15718) != '#skF_3'(k1_tarski(C_15717))
      | k1_tarski(C_15717) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2794])).

tff(c_30113,plain,(
    ! [A_24068,D_24069] :
      ( k4_tarski(A_24068,D_24069) != A_24068
      | k1_tarski(A_24068) = k1_xboole_0
      | k1_tarski(A_24068) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_20697])).

tff(c_30141,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_30113])).

tff(c_30178,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30141,c_4])).

tff(c_30191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_30178])).

tff(c_30193,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30203,plain,(
    ! [A_24625,B_24626] :
      ( r2_hidden(k2_mcart_1(A_24625),B_24626)
      | ~ r2_hidden(A_24625,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_195])).

tff(c_30216,plain,(
    ! [B_24626] :
      ( r2_hidden('#skF_6',B_24626)
      | ~ r2_hidden('#skF_4',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_30203])).

tff(c_30226,plain,(
    ! [B_24627] : r2_hidden('#skF_6',B_24627) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30193,c_30216])).

tff(c_30239,plain,(
    ! [A_1] : A_1 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_30226,c_2])).

tff(c_30240,plain,(
    ! [A_24628] : A_24628 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_30226,c_2])).

tff(c_26,plain,(
    ! [B_15] : k4_xboole_0(k1_tarski(B_15),k1_tarski(B_15)) != k1_tarski(B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30848,plain,(
    ! [B_27995] : k1_tarski(B_27995) != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_30240,c_26])).

tff(c_30862,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_30239,c_30848])).

tff(c_30864,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_30943,plain,(
    ! [A_28146,B_28147,C_28148] :
      ( r2_hidden(k1_mcart_1(A_28146),B_28147)
      | ~ r2_hidden(A_28146,k2_zfmisc_1(B_28147,C_28148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30952,plain,(
    ! [A_28149,A_28150] :
      ( r2_hidden(k1_mcart_1(A_28149),A_28150)
      | ~ r2_hidden(A_28149,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_30943])).

tff(c_30962,plain,(
    ! [A_28150] :
      ( r2_hidden('#skF_5',A_28150)
      | ~ r2_hidden('#skF_4',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_30952])).

tff(c_30978,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_30962])).

tff(c_30863,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_30866,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30863,c_46])).

tff(c_38,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_3'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30888,plain,(
    ! [C_28135,A_28136] :
      ( C_28135 = A_28136
      | ~ r2_hidden(C_28135,k1_tarski(A_28136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30896,plain,(
    ! [A_28136] :
      ( '#skF_3'(k1_tarski(A_28136)) = A_28136
      | k1_tarski(A_28136) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_30888])).

tff(c_34133,plain,(
    ! [D_31399,A_31400,C_31401] :
      ( ~ r2_hidden(D_31399,A_31400)
      | k4_tarski(C_31401,D_31399) != '#skF_3'(A_31400)
      | k1_xboole_0 = A_31400 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_51398,plain,(
    ! [C_43955,C_43956] :
      ( k4_tarski(C_43955,C_43956) != '#skF_3'(k1_tarski(C_43956))
      | k1_tarski(C_43956) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_34133])).

tff(c_59845,plain,(
    ! [C_52586,A_52587] :
      ( k4_tarski(C_52586,A_52587) != A_52587
      | k1_tarski(A_52587) = k1_xboole_0
      | k1_tarski(A_52587) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30896,c_51398])).

tff(c_59873,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30866,c_59845])).

tff(c_59910,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_59873,c_4])).

tff(c_59923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30978,c_59910])).

tff(c_59926,plain,(
    ! [A_53140] : r2_hidden('#skF_5',A_53140) ),
    inference(splitRight,[status(thm)],[c_30962])).

tff(c_59940,plain,(
    ! [A_53141] : A_53141 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_59926,c_2])).

tff(c_59986,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_59940,c_30866])).

tff(c_60021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30864,c_59986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:50:27 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.72/4.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.72/4.68  
% 12.72/4.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.72/4.69  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 12.72/4.69  
% 12.72/4.69  %Foreground sorts:
% 12.72/4.69  
% 12.72/4.69  
% 12.72/4.69  %Background operators:
% 12.72/4.69  
% 12.72/4.69  
% 12.72/4.69  %Foreground operators:
% 12.72/4.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.72/4.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.72/4.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.72/4.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.72/4.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.72/4.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.72/4.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.72/4.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.72/4.69  tff('#skF_5', type, '#skF_5': $i).
% 12.72/4.69  tff('#skF_6', type, '#skF_6': $i).
% 12.72/4.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.72/4.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.72/4.69  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 12.72/4.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.72/4.69  tff('#skF_4', type, '#skF_4': $i).
% 12.72/4.69  tff('#skF_3', type, '#skF_3': $i > $i).
% 12.72/4.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.72/4.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.72/4.69  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 12.72/4.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.72/4.69  
% 12.86/4.70  tff(f_85, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 12.86/4.70  tff(f_59, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 12.86/4.70  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.86/4.70  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 12.86/4.70  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 12.86/4.70  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 12.86/4.70  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 12.86/4.70  tff(c_46, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.86/4.70  tff(c_83, plain, (![A_37, B_38]: (k2_mcart_1(k4_tarski(A_37, B_38))=B_38)), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.86/4.70  tff(c_92, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_46, c_83])).
% 12.86/4.70  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.86/4.70  tff(c_195, plain, (![A_53, C_54, B_55]: (r2_hidden(k2_mcart_1(A_53), C_54) | ~r2_hidden(A_53, k2_zfmisc_1(B_55, C_54)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.86/4.70  tff(c_204, plain, (![A_56]: (r2_hidden(k2_mcart_1(A_56), k1_xboole_0) | ~r2_hidden(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_195])).
% 12.86/4.70  tff(c_207, plain, (r2_hidden('#skF_6', k1_xboole_0) | ~r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92, c_204])).
% 12.86/4.70  tff(c_211, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_207])).
% 12.86/4.70  tff(c_99, plain, (![A_39, B_40]: (k1_mcart_1(k4_tarski(A_39, B_40))=A_39)), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.86/4.70  tff(c_108, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_46, c_99])).
% 12.86/4.70  tff(c_44, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.86/4.70  tff(c_115, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_92, c_44])).
% 12.86/4.70  tff(c_116, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_115])).
% 12.86/4.70  tff(c_118, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_46])).
% 12.86/4.70  tff(c_145, plain, (![A_43]: (r2_hidden('#skF_3'(A_43), A_43) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.86/4.70  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.86/4.70  tff(c_150, plain, (![A_1]: ('#skF_3'(k1_tarski(A_1))=A_1 | k1_tarski(A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_145, c_2])).
% 12.86/4.70  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.86/4.70  tff(c_2794, plain, (![C_3156, A_3157, D_3158]: (~r2_hidden(C_3156, A_3157) | k4_tarski(C_3156, D_3158)!='#skF_3'(A_3157) | k1_xboole_0=A_3157)), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.86/4.70  tff(c_20697, plain, (![C_15717, D_15718]: (k4_tarski(C_15717, D_15718)!='#skF_3'(k1_tarski(C_15717)) | k1_tarski(C_15717)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2794])).
% 12.86/4.70  tff(c_30113, plain, (![A_24068, D_24069]: (k4_tarski(A_24068, D_24069)!=A_24068 | k1_tarski(A_24068)=k1_xboole_0 | k1_tarski(A_24068)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_150, c_20697])).
% 12.86/4.70  tff(c_30141, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_118, c_30113])).
% 12.86/4.70  tff(c_30178, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30141, c_4])).
% 12.86/4.70  tff(c_30191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_30178])).
% 12.86/4.70  tff(c_30193, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_207])).
% 12.86/4.70  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.86/4.70  tff(c_30203, plain, (![A_24625, B_24626]: (r2_hidden(k2_mcart_1(A_24625), B_24626) | ~r2_hidden(A_24625, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_195])).
% 12.86/4.70  tff(c_30216, plain, (![B_24626]: (r2_hidden('#skF_6', B_24626) | ~r2_hidden('#skF_4', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_92, c_30203])).
% 12.86/4.70  tff(c_30226, plain, (![B_24627]: (r2_hidden('#skF_6', B_24627))), inference(demodulation, [status(thm), theory('equality')], [c_30193, c_30216])).
% 12.86/4.70  tff(c_30239, plain, (![A_1]: (A_1='#skF_6')), inference(resolution, [status(thm)], [c_30226, c_2])).
% 12.86/4.70  tff(c_30240, plain, (![A_24628]: (A_24628='#skF_6')), inference(resolution, [status(thm)], [c_30226, c_2])).
% 12.86/4.70  tff(c_26, plain, (![B_15]: (k4_xboole_0(k1_tarski(B_15), k1_tarski(B_15))!=k1_tarski(B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.86/4.70  tff(c_30848, plain, (![B_27995]: (k1_tarski(B_27995)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_30240, c_26])).
% 12.86/4.70  tff(c_30862, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_30239, c_30848])).
% 12.86/4.70  tff(c_30864, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_115])).
% 12.86/4.70  tff(c_30943, plain, (![A_28146, B_28147, C_28148]: (r2_hidden(k1_mcart_1(A_28146), B_28147) | ~r2_hidden(A_28146, k2_zfmisc_1(B_28147, C_28148)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.86/4.70  tff(c_30952, plain, (![A_28149, A_28150]: (r2_hidden(k1_mcart_1(A_28149), A_28150) | ~r2_hidden(A_28149, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_30943])).
% 12.86/4.70  tff(c_30962, plain, (![A_28150]: (r2_hidden('#skF_5', A_28150) | ~r2_hidden('#skF_4', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_108, c_30952])).
% 12.86/4.70  tff(c_30978, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_30962])).
% 12.86/4.70  tff(c_30863, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_115])).
% 12.86/4.70  tff(c_30866, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30863, c_46])).
% 12.86/4.70  tff(c_38, plain, (![A_21]: (r2_hidden('#skF_3'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.86/4.70  tff(c_30888, plain, (![C_28135, A_28136]: (C_28135=A_28136 | ~r2_hidden(C_28135, k1_tarski(A_28136)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.86/4.70  tff(c_30896, plain, (![A_28136]: ('#skF_3'(k1_tarski(A_28136))=A_28136 | k1_tarski(A_28136)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_30888])).
% 12.86/4.70  tff(c_34133, plain, (![D_31399, A_31400, C_31401]: (~r2_hidden(D_31399, A_31400) | k4_tarski(C_31401, D_31399)!='#skF_3'(A_31400) | k1_xboole_0=A_31400)), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.86/4.70  tff(c_51398, plain, (![C_43955, C_43956]: (k4_tarski(C_43955, C_43956)!='#skF_3'(k1_tarski(C_43956)) | k1_tarski(C_43956)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_34133])).
% 12.86/4.70  tff(c_59845, plain, (![C_52586, A_52587]: (k4_tarski(C_52586, A_52587)!=A_52587 | k1_tarski(A_52587)=k1_xboole_0 | k1_tarski(A_52587)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30896, c_51398])).
% 12.86/4.70  tff(c_59873, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_30866, c_59845])).
% 12.86/4.70  tff(c_59910, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_59873, c_4])).
% 12.86/4.70  tff(c_59923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30978, c_59910])).
% 12.86/4.70  tff(c_59926, plain, (![A_53140]: (r2_hidden('#skF_5', A_53140))), inference(splitRight, [status(thm)], [c_30962])).
% 12.86/4.70  tff(c_59940, plain, (![A_53141]: (A_53141='#skF_5')), inference(resolution, [status(thm)], [c_59926, c_2])).
% 12.86/4.70  tff(c_59986, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_59940, c_30866])).
% 12.86/4.70  tff(c_60021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30864, c_59986])).
% 12.86/4.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.86/4.70  
% 12.86/4.70  Inference rules
% 12.86/4.70  ----------------------
% 12.86/4.70  #Ref     : 0
% 12.86/4.70  #Sup     : 12808
% 12.86/4.70  #Fact    : 0
% 12.86/4.70  #Define  : 0
% 12.86/4.70  #Split   : 5
% 12.86/4.70  #Chain   : 0
% 12.86/4.70  #Close   : 0
% 12.86/4.70  
% 12.86/4.70  Ordering : KBO
% 12.86/4.70  
% 12.86/4.70  Simplification rules
% 12.86/4.70  ----------------------
% 12.86/4.70  #Subsume      : 2461
% 12.86/4.70  #Demod        : 1954
% 12.86/4.70  #Tautology    : 120
% 12.86/4.70  #SimpNegUnit  : 5
% 12.86/4.70  #BackRed      : 4
% 12.86/4.70  
% 12.86/4.70  #Partial instantiations: 34863
% 12.86/4.70  #Strategies tried      : 1
% 12.86/4.70  
% 12.86/4.70  Timing (in seconds)
% 12.86/4.70  ----------------------
% 12.86/4.70  Preprocessing        : 0.31
% 12.86/4.70  Parsing              : 0.17
% 12.86/4.70  CNF conversion       : 0.02
% 12.86/4.70  Main loop            : 3.64
% 12.86/4.70  Inferencing          : 1.15
% 12.86/4.70  Reduction            : 0.93
% 12.86/4.70  Demodulation         : 0.65
% 12.86/4.70  BG Simplification    : 0.17
% 12.86/4.70  Subsumption          : 1.05
% 12.86/4.70  Abstraction          : 0.15
% 12.86/4.70  MUC search           : 0.00
% 12.86/4.70  Cooper               : 0.00
% 12.86/4.70  Total                : 3.98
% 12.86/4.70  Index Insertion      : 0.00
% 12.86/4.70  Index Deletion       : 0.00
% 12.86/4.70  Index Matching       : 0.00
% 12.86/4.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
