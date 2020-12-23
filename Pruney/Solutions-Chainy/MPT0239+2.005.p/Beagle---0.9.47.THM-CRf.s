%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:52 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 221 expanded)
%              Number of leaves         :   34 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 397 expanded)
%              Number of equality atoms :   32 ( 232 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_17 > #skF_11 > #skF_15 > #skF_4 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_2 > #skF_8 > #skF_3 > #skF_9 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_91,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_52,plain,(
    ! [C_29] : r2_hidden(C_29,k1_tarski(C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12605,plain,(
    ! [A_37826,B_37827,C_37828,D_37829] :
      ( r2_hidden(k4_tarski(A_37826,B_37827),k2_zfmisc_1(C_37828,D_37829))
      | ~ r2_hidden(B_37827,D_37829)
      | ~ r2_hidden(A_37826,C_37828) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_84,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_17' != '#skF_15'
    | '#skF_16' != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_92,plain,(
    '#skF_16' != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_90,plain,
    ( '#skF_10' = '#skF_12'
    | r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_16'),k1_tarski('#skF_17'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_134,plain,(
    r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_16'),k1_tarski('#skF_17'))) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_343,plain,(
    ! [A_104,C_105,B_106,D_107] :
      ( r2_hidden(A_104,C_105)
      | ~ r2_hidden(k4_tarski(A_104,B_106),k2_zfmisc_1(C_105,D_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_347,plain,(
    r2_hidden('#skF_14',k1_tarski('#skF_16')) ),
    inference(resolution,[status(thm)],[c_134,c_343])).

tff(c_50,plain,(
    ! [C_29,A_25] :
      ( C_29 = A_25
      | ~ r2_hidden(C_29,k1_tarski(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_357,plain,(
    '#skF_16' = '#skF_14' ),
    inference(resolution,[status(thm)],[c_347,c_50])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_357])).

tff(c_363,plain,(
    ~ r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_16'),k1_tarski('#skF_17'))) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_5096,plain,(
    ! [A_18817,B_18818,C_18819,D_18820] :
      ( r2_hidden(k4_tarski(A_18817,B_18818),k2_zfmisc_1(C_18819,D_18820))
      | ~ r2_hidden(B_18818,D_18820)
      | ~ r2_hidden(A_18817,C_18819) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_88,plain,
    ( '#skF_11' = '#skF_13'
    | r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_16'),k1_tarski('#skF_17'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_368,plain,(
    r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_16'),k1_tarski('#skF_17'))) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_368])).

tff(c_475,plain,(
    '#skF_11' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_362,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_86,plain,
    ( ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),k2_zfmisc_1(k1_tarski('#skF_12'),k1_tarski('#skF_13')))
    | r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_16'),k1_tarski('#skF_17'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_558,plain,
    ( ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_12'),k1_tarski('#skF_13')))
    | r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_16'),k1_tarski('#skF_17'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_362,c_86])).

tff(c_559,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_12'),k1_tarski('#skF_13'))) ),
    inference(splitLeft,[status(thm)],[c_558])).

tff(c_5127,plain,
    ( ~ r2_hidden('#skF_13',k1_tarski('#skF_13'))
    | ~ r2_hidden('#skF_12',k1_tarski('#skF_12')) ),
    inference(resolution,[status(thm)],[c_5096,c_559])).

tff(c_5158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_5127])).

tff(c_5159,plain,(
    r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_16'),k1_tarski('#skF_17'))) ),
    inference(splitRight,[status(thm)],[c_558])).

tff(c_5189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_363,c_5159])).

tff(c_5191,plain,(
    '#skF_16' = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_9831,plain,(
    ! [A_34574,B_34575,C_34576,D_34577] :
      ( r2_hidden(k4_tarski(A_34574,B_34575),k2_zfmisc_1(C_34576,D_34577))
      | ~ r2_hidden(B_34575,D_34577)
      | ~ r2_hidden(A_34574,C_34576) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5497,plain,
    ( '#skF_11' = '#skF_13'
    | r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_14'),k1_tarski('#skF_17'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5191,c_88])).

tff(c_5498,plain,(
    r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_14'),k1_tarski('#skF_17'))) ),
    inference(splitLeft,[status(thm)],[c_5497])).

tff(c_5211,plain,
    ( '#skF_10' = '#skF_12'
    | r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_14'),k1_tarski('#skF_17'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5191,c_90])).

tff(c_5212,plain,(
    r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_14'),k1_tarski('#skF_17'))) ),
    inference(splitLeft,[status(thm)],[c_5211])).

tff(c_5190,plain,
    ( '#skF_17' != '#skF_15'
    | '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_5196,plain,(
    '#skF_17' != '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_5190])).

tff(c_5306,plain,
    ( '#skF_11' = '#skF_13'
    | r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_14'),k1_tarski('#skF_17'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5191,c_88])).

tff(c_5307,plain,(
    r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_14'),k1_tarski('#skF_17'))) ),
    inference(splitLeft,[status(thm)],[c_5306])).

tff(c_5433,plain,(
    ! [B_19128,D_19129,A_19130,C_19131] :
      ( r2_hidden(B_19128,D_19129)
      | ~ r2_hidden(k4_tarski(A_19130,B_19128),k2_zfmisc_1(C_19131,D_19129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5437,plain,(
    r2_hidden('#skF_15',k1_tarski('#skF_17')) ),
    inference(resolution,[status(thm)],[c_5307,c_5433])).

tff(c_5440,plain,(
    '#skF_17' = '#skF_15' ),
    inference(resolution,[status(thm)],[c_5437,c_50])).

tff(c_5444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5196,c_5440])).

tff(c_5446,plain,(
    ~ r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_14'),k1_tarski('#skF_17'))) ),
    inference(splitRight,[status(thm)],[c_5306])).

tff(c_5494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5212,c_5446])).

tff(c_5496,plain,(
    ~ r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_14'),k1_tarski('#skF_17'))) ),
    inference(splitRight,[status(thm)],[c_5211])).

tff(c_5641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5498,c_5496])).

tff(c_5642,plain,(
    '#skF_11' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_5497])).

tff(c_5495,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_5211])).

tff(c_5760,plain,
    ( ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_12'),k1_tarski('#skF_13')))
    | r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_14'),k1_tarski('#skF_17'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5191,c_5642,c_5495,c_86])).

tff(c_5761,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_12'),k1_tarski('#skF_13'))) ),
    inference(splitLeft,[status(thm)],[c_5760])).

tff(c_9865,plain,
    ( ~ r2_hidden('#skF_13',k1_tarski('#skF_13'))
    | ~ r2_hidden('#skF_12',k1_tarski('#skF_12')) ),
    inference(resolution,[status(thm)],[c_9831,c_5761])).

tff(c_9896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_9865])).

tff(c_9897,plain,(
    r2_hidden(k4_tarski('#skF_14','#skF_15'),k2_zfmisc_1(k1_tarski('#skF_14'),k1_tarski('#skF_17'))) ),
    inference(splitRight,[status(thm)],[c_5760])).

tff(c_9927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9897,c_5496])).

tff(c_9929,plain,(
    '#skF_17' = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_5190])).

tff(c_82,plain,
    ( '#skF_11' = '#skF_13'
    | '#skF_17' != '#skF_15'
    | '#skF_16' != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_9939,plain,(
    '#skF_11' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5191,c_9929,c_82])).

tff(c_9928,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_5190])).

tff(c_80,plain,
    ( ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),k2_zfmisc_1(k1_tarski('#skF_12'),k1_tarski('#skF_13')))
    | '#skF_17' != '#skF_15'
    | '#skF_16' != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10132,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_12'),k1_tarski('#skF_13'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5191,c_9929,c_9939,c_9928,c_80])).

tff(c_12628,plain,
    ( ~ r2_hidden('#skF_13',k1_tarski('#skF_13'))
    | ~ r2_hidden('#skF_12',k1_tarski('#skF_12')) ),
    inference(resolution,[status(thm)],[c_12605,c_10132])).

tff(c_12644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_12628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.31/2.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.54  
% 7.31/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.54  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_17 > #skF_11 > #skF_15 > #skF_4 > #skF_10 > #skF_16 > #skF_14 > #skF_13 > #skF_2 > #skF_8 > #skF_3 > #skF_9 > #skF_5 > #skF_12
% 7.31/2.54  
% 7.31/2.54  %Foreground sorts:
% 7.31/2.54  
% 7.31/2.54  
% 7.31/2.54  %Background operators:
% 7.31/2.54  
% 7.31/2.54  
% 7.31/2.54  %Foreground operators:
% 7.31/2.54  tff('#skF_7', type, '#skF_7': $i > $i).
% 7.31/2.54  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.31/2.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.31/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.54  tff('#skF_17', type, '#skF_17': $i).
% 7.31/2.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.31/2.54  tff('#skF_11', type, '#skF_11': $i).
% 7.31/2.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.31/2.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.31/2.54  tff('#skF_15', type, '#skF_15': $i).
% 7.31/2.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.31/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.31/2.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.31/2.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.31/2.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.31/2.54  tff('#skF_10', type, '#skF_10': $i).
% 7.31/2.54  tff('#skF_16', type, '#skF_16': $i).
% 7.31/2.54  tff('#skF_14', type, '#skF_14': $i).
% 7.31/2.54  tff('#skF_13', type, '#skF_13': $i).
% 7.31/2.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.31/2.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.31/2.54  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.31/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.31/2.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.31/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.31/2.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.31/2.54  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 7.31/2.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.31/2.54  tff('#skF_12', type, '#skF_12': $i).
% 7.31/2.54  
% 7.31/2.55  tff(f_91, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.31/2.55  tff(f_112, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 7.31/2.55  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 7.31/2.55  tff(c_52, plain, (![C_29]: (r2_hidden(C_29, k1_tarski(C_29)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.31/2.55  tff(c_12605, plain, (![A_37826, B_37827, C_37828, D_37829]: (r2_hidden(k4_tarski(A_37826, B_37827), k2_zfmisc_1(C_37828, D_37829)) | ~r2_hidden(B_37827, D_37829) | ~r2_hidden(A_37826, C_37828))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.31/2.55  tff(c_84, plain, ('#skF_10'='#skF_12' | '#skF_17'!='#skF_15' | '#skF_16'!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.31/2.55  tff(c_92, plain, ('#skF_16'!='#skF_14'), inference(splitLeft, [status(thm)], [c_84])).
% 7.31/2.55  tff(c_90, plain, ('#skF_10'='#skF_12' | r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_16'), k1_tarski('#skF_17')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.31/2.55  tff(c_134, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_16'), k1_tarski('#skF_17')))), inference(splitLeft, [status(thm)], [c_90])).
% 7.31/2.55  tff(c_343, plain, (![A_104, C_105, B_106, D_107]: (r2_hidden(A_104, C_105) | ~r2_hidden(k4_tarski(A_104, B_106), k2_zfmisc_1(C_105, D_107)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.31/2.55  tff(c_347, plain, (r2_hidden('#skF_14', k1_tarski('#skF_16'))), inference(resolution, [status(thm)], [c_134, c_343])).
% 7.31/2.55  tff(c_50, plain, (![C_29, A_25]: (C_29=A_25 | ~r2_hidden(C_29, k1_tarski(A_25)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.31/2.55  tff(c_357, plain, ('#skF_16'='#skF_14'), inference(resolution, [status(thm)], [c_347, c_50])).
% 7.31/2.55  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_357])).
% 7.31/2.55  tff(c_363, plain, (~r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_16'), k1_tarski('#skF_17')))), inference(splitRight, [status(thm)], [c_90])).
% 7.31/2.55  tff(c_5096, plain, (![A_18817, B_18818, C_18819, D_18820]: (r2_hidden(k4_tarski(A_18817, B_18818), k2_zfmisc_1(C_18819, D_18820)) | ~r2_hidden(B_18818, D_18820) | ~r2_hidden(A_18817, C_18819))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.31/2.55  tff(c_88, plain, ('#skF_11'='#skF_13' | r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_16'), k1_tarski('#skF_17')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.31/2.55  tff(c_368, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_16'), k1_tarski('#skF_17')))), inference(splitLeft, [status(thm)], [c_88])).
% 7.31/2.55  tff(c_474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_363, c_368])).
% 7.31/2.55  tff(c_475, plain, ('#skF_11'='#skF_13'), inference(splitRight, [status(thm)], [c_88])).
% 7.31/2.55  tff(c_362, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_90])).
% 7.31/2.55  tff(c_86, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), k2_zfmisc_1(k1_tarski('#skF_12'), k1_tarski('#skF_13'))) | r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_16'), k1_tarski('#skF_17')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.31/2.55  tff(c_558, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_12'), k1_tarski('#skF_13'))) | r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_16'), k1_tarski('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_475, c_362, c_86])).
% 7.31/2.55  tff(c_559, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_12'), k1_tarski('#skF_13')))), inference(splitLeft, [status(thm)], [c_558])).
% 7.31/2.55  tff(c_5127, plain, (~r2_hidden('#skF_13', k1_tarski('#skF_13')) | ~r2_hidden('#skF_12', k1_tarski('#skF_12'))), inference(resolution, [status(thm)], [c_5096, c_559])).
% 7.31/2.55  tff(c_5158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_5127])).
% 7.31/2.55  tff(c_5159, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_16'), k1_tarski('#skF_17')))), inference(splitRight, [status(thm)], [c_558])).
% 7.31/2.55  tff(c_5189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_363, c_5159])).
% 7.31/2.55  tff(c_5191, plain, ('#skF_16'='#skF_14'), inference(splitRight, [status(thm)], [c_84])).
% 7.31/2.55  tff(c_9831, plain, (![A_34574, B_34575, C_34576, D_34577]: (r2_hidden(k4_tarski(A_34574, B_34575), k2_zfmisc_1(C_34576, D_34577)) | ~r2_hidden(B_34575, D_34577) | ~r2_hidden(A_34574, C_34576))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.31/2.55  tff(c_5497, plain, ('#skF_11'='#skF_13' | r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_14'), k1_tarski('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_5191, c_88])).
% 7.31/2.55  tff(c_5498, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_14'), k1_tarski('#skF_17')))), inference(splitLeft, [status(thm)], [c_5497])).
% 7.31/2.55  tff(c_5211, plain, ('#skF_10'='#skF_12' | r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_14'), k1_tarski('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_5191, c_90])).
% 7.31/2.55  tff(c_5212, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_14'), k1_tarski('#skF_17')))), inference(splitLeft, [status(thm)], [c_5211])).
% 7.31/2.55  tff(c_5190, plain, ('#skF_17'!='#skF_15' | '#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_84])).
% 7.31/2.55  tff(c_5196, plain, ('#skF_17'!='#skF_15'), inference(splitLeft, [status(thm)], [c_5190])).
% 7.31/2.55  tff(c_5306, plain, ('#skF_11'='#skF_13' | r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_14'), k1_tarski('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_5191, c_88])).
% 7.31/2.55  tff(c_5307, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_14'), k1_tarski('#skF_17')))), inference(splitLeft, [status(thm)], [c_5306])).
% 7.31/2.55  tff(c_5433, plain, (![B_19128, D_19129, A_19130, C_19131]: (r2_hidden(B_19128, D_19129) | ~r2_hidden(k4_tarski(A_19130, B_19128), k2_zfmisc_1(C_19131, D_19129)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.31/2.55  tff(c_5437, plain, (r2_hidden('#skF_15', k1_tarski('#skF_17'))), inference(resolution, [status(thm)], [c_5307, c_5433])).
% 7.31/2.55  tff(c_5440, plain, ('#skF_17'='#skF_15'), inference(resolution, [status(thm)], [c_5437, c_50])).
% 7.31/2.55  tff(c_5444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5196, c_5440])).
% 7.31/2.55  tff(c_5446, plain, (~r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_14'), k1_tarski('#skF_17')))), inference(splitRight, [status(thm)], [c_5306])).
% 7.31/2.55  tff(c_5494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5212, c_5446])).
% 7.31/2.55  tff(c_5496, plain, (~r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_14'), k1_tarski('#skF_17')))), inference(splitRight, [status(thm)], [c_5211])).
% 7.31/2.55  tff(c_5641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5498, c_5496])).
% 7.31/2.55  tff(c_5642, plain, ('#skF_11'='#skF_13'), inference(splitRight, [status(thm)], [c_5497])).
% 7.31/2.55  tff(c_5495, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_5211])).
% 7.31/2.55  tff(c_5760, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_12'), k1_tarski('#skF_13'))) | r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_14'), k1_tarski('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_5191, c_5642, c_5495, c_86])).
% 7.31/2.55  tff(c_5761, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_12'), k1_tarski('#skF_13')))), inference(splitLeft, [status(thm)], [c_5760])).
% 7.31/2.55  tff(c_9865, plain, (~r2_hidden('#skF_13', k1_tarski('#skF_13')) | ~r2_hidden('#skF_12', k1_tarski('#skF_12'))), inference(resolution, [status(thm)], [c_9831, c_5761])).
% 7.31/2.55  tff(c_9896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_9865])).
% 7.31/2.55  tff(c_9897, plain, (r2_hidden(k4_tarski('#skF_14', '#skF_15'), k2_zfmisc_1(k1_tarski('#skF_14'), k1_tarski('#skF_17')))), inference(splitRight, [status(thm)], [c_5760])).
% 7.31/2.55  tff(c_9927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9897, c_5496])).
% 7.31/2.55  tff(c_9929, plain, ('#skF_17'='#skF_15'), inference(splitRight, [status(thm)], [c_5190])).
% 7.31/2.55  tff(c_82, plain, ('#skF_11'='#skF_13' | '#skF_17'!='#skF_15' | '#skF_16'!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.31/2.55  tff(c_9939, plain, ('#skF_11'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_5191, c_9929, c_82])).
% 7.31/2.55  tff(c_9928, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_5190])).
% 7.31/2.55  tff(c_80, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), k2_zfmisc_1(k1_tarski('#skF_12'), k1_tarski('#skF_13'))) | '#skF_17'!='#skF_15' | '#skF_16'!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.31/2.55  tff(c_10132, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_12'), k1_tarski('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_5191, c_9929, c_9939, c_9928, c_80])).
% 7.31/2.55  tff(c_12628, plain, (~r2_hidden('#skF_13', k1_tarski('#skF_13')) | ~r2_hidden('#skF_12', k1_tarski('#skF_12'))), inference(resolution, [status(thm)], [c_12605, c_10132])).
% 7.31/2.55  tff(c_12644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_12628])).
% 7.31/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.55  
% 7.31/2.55  Inference rules
% 7.31/2.55  ----------------------
% 7.31/2.55  #Ref     : 0
% 7.31/2.55  #Sup     : 1686
% 7.31/2.55  #Fact    : 0
% 7.31/2.55  #Define  : 0
% 7.31/2.55  #Split   : 14
% 7.31/2.55  #Chain   : 0
% 7.31/2.55  #Close   : 0
% 7.31/2.55  
% 7.31/2.55  Ordering : KBO
% 7.31/2.55  
% 7.31/2.56  Simplification rules
% 7.31/2.56  ----------------------
% 7.31/2.56  #Subsume      : 253
% 7.31/2.56  #Demod        : 976
% 7.31/2.56  #Tautology    : 515
% 7.31/2.56  #SimpNegUnit  : 88
% 7.31/2.56  #BackRed      : 37
% 7.31/2.56  
% 7.31/2.56  #Partial instantiations: 18188
% 7.31/2.56  #Strategies tried      : 1
% 7.31/2.56  
% 7.31/2.56  Timing (in seconds)
% 7.31/2.56  ----------------------
% 7.31/2.56  Preprocessing        : 0.36
% 7.31/2.56  Parsing              : 0.18
% 7.31/2.56  CNF conversion       : 0.03
% 7.31/2.56  Main loop            : 1.37
% 7.31/2.56  Inferencing          : 0.73
% 7.31/2.56  Reduction            : 0.30
% 7.31/2.56  Demodulation         : 0.20
% 7.31/2.56  BG Simplification    : 0.06
% 7.31/2.56  Subsumption          : 0.19
% 7.31/2.56  Abstraction          : 0.07
% 7.31/2.56  MUC search           : 0.00
% 7.31/2.56  Cooper               : 0.00
% 7.31/2.56  Total                : 1.76
% 7.31/2.56  Index Insertion      : 0.00
% 7.31/2.56  Index Deletion       : 0.00
% 7.31/2.56  Index Matching       : 0.00
% 7.31/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
