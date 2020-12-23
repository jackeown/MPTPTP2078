%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:00 EST 2020

% Result     : Theorem 6.47s
% Output     : CNFRefutation 6.50s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 135 expanded)
%              Number of leaves         :   36 (  64 expanded)
%              Depth                    :    6
%              Number of atoms          :   80 ( 213 expanded)
%              Number of equality atoms :   17 (  69 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_15 > #skF_10 > #skF_14 > #skF_2 > #skF_13 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_92,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_15' != '#skF_13'
    | ~ r2_hidden('#skF_12','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_131,plain,(
    ~ r2_hidden('#skF_12','#skF_14') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_98,plain,
    ( '#skF_11' = '#skF_9'
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14',k1_tarski('#skF_15'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_251,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14',k1_tarski('#skF_15'))) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_344,plain,(
    ! [A_118,C_119,B_120,D_121] :
      ( r2_hidden(A_118,C_119)
      | ~ r2_hidden(k4_tarski(A_118,B_120),k2_zfmisc_1(C_119,D_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_347,plain,(
    r2_hidden('#skF_12','#skF_14') ),
    inference(resolution,[status(thm)],[c_251,c_344])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_347])).

tff(c_353,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14',k1_tarski('#skF_15'))) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_100,plain,
    ( r2_hidden('#skF_8','#skF_10')
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14',k1_tarski('#skF_15'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_380,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_100])).

tff(c_34,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3383,plain,(
    ! [A_414,B_415,C_416,D_417] :
      ( r2_hidden(k4_tarski(A_414,B_415),k2_zfmisc_1(C_416,D_417))
      | ~ r2_hidden(B_415,D_417)
      | ~ r2_hidden(A_414,C_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_352,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_96,plain,
    ( ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14',k1_tarski('#skF_15'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_603,plain,
    ( ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1('#skF_10',k1_tarski('#skF_9')))
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14',k1_tarski('#skF_15'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_96])).

tff(c_604,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1('#skF_10',k1_tarski('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_603])).

tff(c_3388,plain,
    ( ~ r2_hidden('#skF_9',k1_tarski('#skF_9'))
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_3383,c_604])).

tff(c_3404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_34,c_3388])).

tff(c_3406,plain,(
    r2_hidden('#skF_12','#skF_14') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_3854,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14',k1_tarski('#skF_15'))) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_3405,plain,
    ( '#skF_15' != '#skF_13'
    | '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_3407,plain,(
    '#skF_15' != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_3405])).

tff(c_3461,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14',k1_tarski('#skF_15'))) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_3828,plain,(
    ! [B_498,D_499,A_500,C_501] :
      ( r2_hidden(B_498,D_499)
      | ~ r2_hidden(k4_tarski(A_500,B_498),k2_zfmisc_1(C_501,D_499)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3832,plain,(
    r2_hidden('#skF_13',k1_tarski('#skF_15')) ),
    inference(resolution,[status(thm)],[c_3461,c_3828])).

tff(c_32,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3837,plain,(
    '#skF_15' = '#skF_13' ),
    inference(resolution,[status(thm)],[c_3832,c_32])).

tff(c_3842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3407,c_3837])).

tff(c_3844,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14',k1_tarski('#skF_15'))) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_3885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3854,c_3844])).

tff(c_3886,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_5432,plain,(
    ! [A_690,B_691,C_692,D_693] :
      ( r2_hidden(k4_tarski(A_690,B_691),k2_zfmisc_1(C_692,D_693))
      | ~ r2_hidden(B_691,D_693)
      | ~ r2_hidden(A_690,C_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3887,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14',k1_tarski('#skF_15'))) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_3843,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_3988,plain,
    ( ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1('#skF_10',k1_tarski('#skF_9')))
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1('#skF_14',k1_tarski('#skF_15'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3843,c_96])).

tff(c_3989,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1('#skF_10',k1_tarski('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3887,c_3988])).

tff(c_5443,plain,
    ( ~ r2_hidden('#skF_9',k1_tarski('#skF_9'))
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_5432,c_3989])).

tff(c_5455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3886,c_34,c_5443])).

tff(c_5457,plain,(
    '#skF_15' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_3405])).

tff(c_94,plain,
    ( r2_hidden('#skF_8','#skF_10')
    | '#skF_15' != '#skF_13'
    | ~ r2_hidden('#skF_12','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5468,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3406,c_5457,c_94])).

tff(c_7002,plain,(
    ! [A_883,B_884,C_885,D_886] :
      ( r2_hidden(k4_tarski(A_883,B_884),k2_zfmisc_1(C_885,D_886))
      | ~ r2_hidden(B_884,D_886)
      | ~ r2_hidden(A_883,C_885) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5456,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3405])).

tff(c_90,plain,
    ( ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))
    | '#skF_15' != '#skF_13'
    | ~ r2_hidden('#skF_12','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5727,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1('#skF_10',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3406,c_5457,c_5456,c_90])).

tff(c_7010,plain,
    ( ~ r2_hidden('#skF_9',k1_tarski('#skF_9'))
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_7002,c_5727])).

tff(c_7021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5468,c_34,c_7010])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.47/2.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.42  
% 6.50/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.42  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_15 > #skF_10 > #skF_14 > #skF_2 > #skF_13 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_12 > #skF_4
% 6.50/2.42  
% 6.50/2.42  %Foreground sorts:
% 6.50/2.42  
% 6.50/2.42  
% 6.50/2.42  %Background operators:
% 6.50/2.42  
% 6.50/2.42  
% 6.50/2.42  %Foreground operators:
% 6.50/2.42  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.50/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.50/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.50/2.42  tff('#skF_11', type, '#skF_11': $i).
% 6.50/2.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.50/2.42  tff('#skF_15', type, '#skF_15': $i).
% 6.50/2.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.50/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.50/2.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.50/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.50/2.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.50/2.42  tff('#skF_10', type, '#skF_10': $i).
% 6.50/2.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.50/2.42  tff('#skF_14', type, '#skF_14': $i).
% 6.50/2.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.50/2.42  tff('#skF_13', type, '#skF_13': $i).
% 6.50/2.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.50/2.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.50/2.42  tff('#skF_9', type, '#skF_9': $i).
% 6.50/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.50/2.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.50/2.42  tff('#skF_8', type, '#skF_8': $i).
% 6.50/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.50/2.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.50/2.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.50/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.50/2.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.50/2.42  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 6.50/2.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.50/2.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.50/2.42  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.50/2.42  tff('#skF_12', type, '#skF_12': $i).
% 6.50/2.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.50/2.42  
% 6.50/2.44  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 6.50/2.44  tff(f_81, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 6.50/2.44  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.50/2.44  tff(c_92, plain, ('#skF_11'='#skF_9' | '#skF_15'!='#skF_13' | ~r2_hidden('#skF_12', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.50/2.44  tff(c_131, plain, (~r2_hidden('#skF_12', '#skF_14')), inference(splitLeft, [status(thm)], [c_92])).
% 6.50/2.44  tff(c_98, plain, ('#skF_11'='#skF_9' | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', k1_tarski('#skF_15')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.50/2.44  tff(c_251, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', k1_tarski('#skF_15')))), inference(splitLeft, [status(thm)], [c_98])).
% 6.50/2.44  tff(c_344, plain, (![A_118, C_119, B_120, D_121]: (r2_hidden(A_118, C_119) | ~r2_hidden(k4_tarski(A_118, B_120), k2_zfmisc_1(C_119, D_121)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.50/2.44  tff(c_347, plain, (r2_hidden('#skF_12', '#skF_14')), inference(resolution, [status(thm)], [c_251, c_344])).
% 6.50/2.44  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_347])).
% 6.50/2.44  tff(c_353, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', k1_tarski('#skF_15')))), inference(splitRight, [status(thm)], [c_98])).
% 6.50/2.44  tff(c_100, plain, (r2_hidden('#skF_8', '#skF_10') | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', k1_tarski('#skF_15')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.50/2.44  tff(c_380, plain, (r2_hidden('#skF_8', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_353, c_100])).
% 6.50/2.44  tff(c_34, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.50/2.44  tff(c_3383, plain, (![A_414, B_415, C_416, D_417]: (r2_hidden(k4_tarski(A_414, B_415), k2_zfmisc_1(C_416, D_417)) | ~r2_hidden(B_415, D_417) | ~r2_hidden(A_414, C_416))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.50/2.44  tff(c_352, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_98])).
% 6.50/2.44  tff(c_96, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))) | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', k1_tarski('#skF_15')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.50/2.44  tff(c_603, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_10', k1_tarski('#skF_9'))) | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', k1_tarski('#skF_15')))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_96])).
% 6.50/2.44  tff(c_604, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_10', k1_tarski('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_353, c_603])).
% 6.50/2.44  tff(c_3388, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9')) | ~r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_3383, c_604])).
% 6.50/2.44  tff(c_3404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_380, c_34, c_3388])).
% 6.50/2.44  tff(c_3406, plain, (r2_hidden('#skF_12', '#skF_14')), inference(splitRight, [status(thm)], [c_92])).
% 6.50/2.44  tff(c_3854, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', k1_tarski('#skF_15')))), inference(splitLeft, [status(thm)], [c_100])).
% 6.50/2.44  tff(c_3405, plain, ('#skF_15'!='#skF_13' | '#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_92])).
% 6.50/2.44  tff(c_3407, plain, ('#skF_15'!='#skF_13'), inference(splitLeft, [status(thm)], [c_3405])).
% 6.50/2.44  tff(c_3461, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', k1_tarski('#skF_15')))), inference(splitLeft, [status(thm)], [c_98])).
% 6.50/2.44  tff(c_3828, plain, (![B_498, D_499, A_500, C_501]: (r2_hidden(B_498, D_499) | ~r2_hidden(k4_tarski(A_500, B_498), k2_zfmisc_1(C_501, D_499)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.50/2.44  tff(c_3832, plain, (r2_hidden('#skF_13', k1_tarski('#skF_15'))), inference(resolution, [status(thm)], [c_3461, c_3828])).
% 6.50/2.44  tff(c_32, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.50/2.44  tff(c_3837, plain, ('#skF_15'='#skF_13'), inference(resolution, [status(thm)], [c_3832, c_32])).
% 6.50/2.44  tff(c_3842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3407, c_3837])).
% 6.50/2.44  tff(c_3844, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', k1_tarski('#skF_15')))), inference(splitRight, [status(thm)], [c_98])).
% 6.50/2.44  tff(c_3885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3854, c_3844])).
% 6.50/2.44  tff(c_3886, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_100])).
% 6.50/2.44  tff(c_5432, plain, (![A_690, B_691, C_692, D_693]: (r2_hidden(k4_tarski(A_690, B_691), k2_zfmisc_1(C_692, D_693)) | ~r2_hidden(B_691, D_693) | ~r2_hidden(A_690, C_692))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.50/2.44  tff(c_3887, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', k1_tarski('#skF_15')))), inference(splitRight, [status(thm)], [c_100])).
% 6.50/2.44  tff(c_3843, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_98])).
% 6.50/2.44  tff(c_3988, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_10', k1_tarski('#skF_9'))) | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1('#skF_14', k1_tarski('#skF_15')))), inference(demodulation, [status(thm), theory('equality')], [c_3843, c_96])).
% 6.50/2.44  tff(c_3989, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_10', k1_tarski('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_3887, c_3988])).
% 6.50/2.44  tff(c_5443, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9')) | ~r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_5432, c_3989])).
% 6.50/2.44  tff(c_5455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3886, c_34, c_5443])).
% 6.50/2.44  tff(c_5457, plain, ('#skF_15'='#skF_13'), inference(splitRight, [status(thm)], [c_3405])).
% 6.50/2.44  tff(c_94, plain, (r2_hidden('#skF_8', '#skF_10') | '#skF_15'!='#skF_13' | ~r2_hidden('#skF_12', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.50/2.44  tff(c_5468, plain, (r2_hidden('#skF_8', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_3406, c_5457, c_94])).
% 6.50/2.44  tff(c_7002, plain, (![A_883, B_884, C_885, D_886]: (r2_hidden(k4_tarski(A_883, B_884), k2_zfmisc_1(C_885, D_886)) | ~r2_hidden(B_884, D_886) | ~r2_hidden(A_883, C_885))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.50/2.44  tff(c_5456, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_3405])).
% 6.50/2.44  tff(c_90, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))) | '#skF_15'!='#skF_13' | ~r2_hidden('#skF_12', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.50/2.44  tff(c_5727, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1('#skF_10', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_3406, c_5457, c_5456, c_90])).
% 6.50/2.44  tff(c_7010, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9')) | ~r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_7002, c_5727])).
% 6.50/2.44  tff(c_7021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5468, c_34, c_7010])).
% 6.50/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.44  
% 6.50/2.44  Inference rules
% 6.50/2.44  ----------------------
% 6.50/2.44  #Ref     : 0
% 6.50/2.44  #Sup     : 1521
% 6.50/2.44  #Fact    : 0
% 6.50/2.44  #Define  : 0
% 6.50/2.44  #Split   : 16
% 6.50/2.44  #Chain   : 0
% 6.50/2.44  #Close   : 0
% 6.50/2.44  
% 6.50/2.44  Ordering : KBO
% 6.50/2.44  
% 6.50/2.44  Simplification rules
% 6.50/2.44  ----------------------
% 6.50/2.44  #Subsume      : 115
% 6.50/2.44  #Demod        : 281
% 6.50/2.44  #Tautology    : 299
% 6.50/2.44  #SimpNegUnit  : 5
% 6.50/2.44  #BackRed      : 0
% 6.50/2.44  
% 6.50/2.44  #Partial instantiations: 0
% 6.50/2.44  #Strategies tried      : 1
% 6.50/2.44  
% 6.50/2.44  Timing (in seconds)
% 6.50/2.44  ----------------------
% 6.50/2.44  Preprocessing        : 0.35
% 6.50/2.44  Parsing              : 0.18
% 6.50/2.44  CNF conversion       : 0.03
% 6.50/2.44  Main loop            : 1.31
% 6.50/2.44  Inferencing          : 0.42
% 6.50/2.44  Reduction            : 0.44
% 6.50/2.44  Demodulation         : 0.33
% 6.50/2.44  BG Simplification    : 0.05
% 6.50/2.44  Subsumption          : 0.29
% 6.50/2.44  Abstraction          : 0.05
% 6.50/2.44  MUC search           : 0.00
% 6.50/2.44  Cooper               : 0.00
% 6.50/2.44  Total                : 1.69
% 6.50/2.44  Index Insertion      : 0.00
% 6.50/2.44  Index Deletion       : 0.00
% 6.50/2.44  Index Matching       : 0.00
% 6.50/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
