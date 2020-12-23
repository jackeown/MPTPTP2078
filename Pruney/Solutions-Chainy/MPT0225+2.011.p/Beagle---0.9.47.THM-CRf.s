%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:32 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 276 expanded)
%              Number of leaves         :   34 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  110 ( 430 expanded)
%              Number of equality atoms :   64 ( 298 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_112,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_81,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_60,plain,(
    ! [B_52] : r1_tarski(k1_xboole_0,k1_tarski(B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_58,plain,(
    ! [B_52] : r1_tarski(k1_tarski(B_52),k1_tarski(B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10762,plain,(
    ! [A_1396,B_1397] :
      ( k4_xboole_0(A_1396,B_1397) = k1_xboole_0
      | ~ r1_tarski(A_1396,B_1397) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10782,plain,(
    ! [B_52] : k4_xboole_0(k1_tarski(B_52),k1_tarski(B_52)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_10762])).

tff(c_66,plain,
    ( '#skF_7' != '#skF_6'
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_71,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_529,plain,(
    ! [B_107,A_108] :
      ( k1_tarski(B_107) = A_108
      | k1_xboole_0 = A_108
      | ~ r1_tarski(A_108,k1_tarski(B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10046,plain,(
    ! [B_331,B_332] :
      ( k4_xboole_0(k1_tarski(B_331),B_332) = k1_tarski(B_331)
      | k4_xboole_0(k1_tarski(B_331),B_332) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_529])).

tff(c_64,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_220,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_10183,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10046,c_220])).

tff(c_245,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(A_79,B_80)
      | k4_xboole_0(A_79,B_80) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_62,plain,(
    ! [B_54,A_53] :
      ( B_54 = A_53
      | ~ r1_tarski(k1_tarski(A_53),k1_tarski(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_256,plain,(
    ! [B_54,A_53] :
      ( B_54 = A_53
      | k4_xboole_0(k1_tarski(A_53),k1_tarski(B_54)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_245,c_62])).

tff(c_10267,plain,(
    '#skF_7' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_10183,c_256])).

tff(c_10317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_10267])).

tff(c_10319,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_167,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k1_xboole_0
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_183,plain,(
    ! [B_52] : k4_xboole_0(k1_tarski(B_52),k1_tarski(B_52)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_167])).

tff(c_10318,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_10342,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_10318,c_68])).

tff(c_10343,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_10342])).

tff(c_10499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10319,c_10343])).

tff(c_10500,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10342])).

tff(c_10543,plain,(
    ! [B_345,A_346] :
      ( B_345 = A_346
      | ~ r1_tarski(k1_tarski(A_346),k1_tarski(B_345)) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_10546,plain,(
    ! [B_345] :
      ( B_345 = '#skF_8'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(B_345)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10500,c_10543])).

tff(c_10554,plain,(
    ! [B_345] : B_345 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_10546])).

tff(c_10557,plain,(
    ! [B_347] : B_347 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_10546])).

tff(c_10621,plain,(
    '#skF_6' != '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_10557,c_71])).

tff(c_10639,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_10554,c_10621])).

tff(c_10640,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_10641,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_70,plain,
    ( '#skF_7' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_10693,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10640,c_10641,c_70])).

tff(c_10839,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10782,c_10693])).

tff(c_10900,plain,(
    ! [B_1405,A_1406] :
      ( B_1405 = A_1406
      | ~ r1_tarski(k1_tarski(A_1406),k1_tarski(B_1405)) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_10903,plain,(
    ! [B_1405] :
      ( B_1405 = '#skF_8'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(B_1405)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10839,c_10900])).

tff(c_10918,plain,(
    ! [B_1407] : B_1407 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_10903])).

tff(c_38,plain,(
    ! [C_36] : r2_hidden(C_36,k1_tarski(C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10984,plain,(
    ! [C_36] : r2_hidden(C_36,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_10918,c_38])).

tff(c_10914,plain,(
    ! [B_1405] : B_1405 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_10903])).

tff(c_11019,plain,(
    ! [A_2580,B_2581,C_2582] :
      ( ~ r1_xboole_0(A_2580,B_2581)
      | ~ r2_hidden(C_2582,k3_xboole_0(A_2580,B_2581)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_11021,plain,(
    ! [A_2580,B_2581,C_2582] :
      ( ~ r1_xboole_0(A_2580,B_2581)
      | ~ r2_hidden(C_2582,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10914,c_11019])).

tff(c_11030,plain,(
    ! [A_2580,B_2581] : ~ r1_xboole_0(A_2580,B_2581) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10984,c_11021])).

tff(c_28,plain,(
    ! [A_22,C_24,B_23] :
      ( r1_xboole_0(A_22,k4_xboole_0(C_24,B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14308,plain,(
    ! [A_22,B_23] : ~ r1_tarski(A_22,B_23) ),
    inference(negUnitSimplification,[status(thm)],[c_11030,c_28])).

tff(c_10756,plain,(
    ! [A_1394,B_1395] :
      ( r1_tarski(A_1394,B_1395)
      | k4_xboole_0(A_1394,B_1395) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10761,plain,(
    ! [A_1394] :
      ( k1_xboole_0 = A_1394
      | k4_xboole_0(A_1394,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10756,c_26])).

tff(c_10944,plain,(
    ! [A_1394] :
      ( k1_xboole_0 = A_1394
      | k1_xboole_0 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10918,c_10761])).

tff(c_11044,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_10944])).

tff(c_11048,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_10914,c_11044])).

tff(c_11051,plain,(
    ! [A_2742] : k1_xboole_0 = A_2742 ),
    inference(splitRight,[status(thm)],[c_10944])).

tff(c_11077,plain,(
    ! [B_54,A_53] :
      ( B_54 = A_53
      | ~ r1_tarski(k1_xboole_0,k1_tarski(B_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11051,c_62])).

tff(c_13771,plain,(
    ! [B_54] : B_54 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_11077])).

tff(c_11114,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_10944])).

tff(c_10671,plain,(
    ! [A_1385,B_1386] : r1_tarski(k4_xboole_0(A_1385,B_1386),A_1385) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10677,plain,(
    ! [B_1387] : k4_xboole_0(k1_xboole_0,B_1387) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10671,c_26])).

tff(c_10682,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10677,c_24])).

tff(c_11115,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11114,c_10682])).

tff(c_13773,plain,(
    r1_tarski('#skF_9','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_13771,c_11115])).

tff(c_14319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14308,c_13773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:40:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.47/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.69  
% 7.47/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 7.47/2.70  
% 7.47/2.70  %Foreground sorts:
% 7.47/2.70  
% 7.47/2.70  
% 7.47/2.70  %Background operators:
% 7.47/2.70  
% 7.47/2.70  
% 7.47/2.70  %Foreground operators:
% 7.47/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.47/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.47/2.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.47/2.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.47/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.47/2.70  tff('#skF_7', type, '#skF_7': $i).
% 7.47/2.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.47/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.47/2.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.47/2.70  tff('#skF_6', type, '#skF_6': $i).
% 7.47/2.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.47/2.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.47/2.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.47/2.70  tff('#skF_9', type, '#skF_9': $i).
% 7.47/2.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.47/2.70  tff('#skF_8', type, '#skF_8': $i).
% 7.47/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.47/2.70  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.47/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.47/2.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.47/2.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.47/2.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.47/2.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.47/2.70  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.47/2.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.47/2.70  
% 7.47/2.71  tff(f_112, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 7.47/2.71  tff(f_71, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.47/2.71  tff(f_122, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 7.47/2.71  tff(f_77, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.47/2.71  tff(f_116, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 7.47/2.71  tff(f_98, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.47/2.71  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.47/2.71  tff(f_85, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 7.47/2.71  tff(f_81, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.47/2.71  tff(c_60, plain, (![B_52]: (r1_tarski(k1_xboole_0, k1_tarski(B_52)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.47/2.71  tff(c_58, plain, (![B_52]: (r1_tarski(k1_tarski(B_52), k1_tarski(B_52)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.47/2.71  tff(c_10762, plain, (![A_1396, B_1397]: (k4_xboole_0(A_1396, B_1397)=k1_xboole_0 | ~r1_tarski(A_1396, B_1397))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.47/2.71  tff(c_10782, plain, (![B_52]: (k4_xboole_0(k1_tarski(B_52), k1_tarski(B_52))=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_10762])).
% 7.47/2.71  tff(c_66, plain, ('#skF_7'!='#skF_6' | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.47/2.71  tff(c_71, plain, ('#skF_7'!='#skF_6'), inference(splitLeft, [status(thm)], [c_66])).
% 7.47/2.71  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.47/2.71  tff(c_529, plain, (![B_107, A_108]: (k1_tarski(B_107)=A_108 | k1_xboole_0=A_108 | ~r1_tarski(A_108, k1_tarski(B_107)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.47/2.71  tff(c_10046, plain, (![B_331, B_332]: (k4_xboole_0(k1_tarski(B_331), B_332)=k1_tarski(B_331) | k4_xboole_0(k1_tarski(B_331), B_332)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_529])).
% 7.47/2.71  tff(c_64, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.47/2.71  tff(c_220, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_64])).
% 7.47/2.71  tff(c_10183, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10046, c_220])).
% 7.47/2.71  tff(c_245, plain, (![A_79, B_80]: (r1_tarski(A_79, B_80) | k4_xboole_0(A_79, B_80)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.47/2.71  tff(c_62, plain, (![B_54, A_53]: (B_54=A_53 | ~r1_tarski(k1_tarski(A_53), k1_tarski(B_54)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.47/2.71  tff(c_256, plain, (![B_54, A_53]: (B_54=A_53 | k4_xboole_0(k1_tarski(A_53), k1_tarski(B_54))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_245, c_62])).
% 7.47/2.71  tff(c_10267, plain, ('#skF_7'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_10183, c_256])).
% 7.47/2.71  tff(c_10317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_10267])).
% 7.47/2.71  tff(c_10319, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_64])).
% 7.47/2.71  tff(c_167, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k1_xboole_0 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.47/2.71  tff(c_183, plain, (![B_52]: (k4_xboole_0(k1_tarski(B_52), k1_tarski(B_52))=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_167])).
% 7.47/2.71  tff(c_10318, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_64])).
% 7.47/2.71  tff(c_68, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.47/2.71  tff(c_10342, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_183, c_10318, c_68])).
% 7.47/2.71  tff(c_10343, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_10342])).
% 7.47/2.71  tff(c_10499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10319, c_10343])).
% 7.47/2.71  tff(c_10500, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_10342])).
% 7.47/2.71  tff(c_10543, plain, (![B_345, A_346]: (B_345=A_346 | ~r1_tarski(k1_tarski(A_346), k1_tarski(B_345)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.47/2.71  tff(c_10546, plain, (![B_345]: (B_345='#skF_8' | ~r1_tarski(k1_xboole_0, k1_tarski(B_345)))), inference(superposition, [status(thm), theory('equality')], [c_10500, c_10543])).
% 7.47/2.71  tff(c_10554, plain, (![B_345]: (B_345='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_10546])).
% 7.47/2.71  tff(c_10557, plain, (![B_347]: (B_347='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_10546])).
% 7.47/2.71  tff(c_10621, plain, ('#skF_6'!='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_10557, c_71])).
% 7.47/2.71  tff(c_10639, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_10554, c_10621])).
% 7.47/2.71  tff(c_10640, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_66])).
% 7.47/2.71  tff(c_10641, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_66])).
% 7.47/2.71  tff(c_70, plain, ('#skF_7'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.47/2.71  tff(c_10693, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10640, c_10641, c_70])).
% 7.47/2.71  tff(c_10839, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10782, c_10693])).
% 7.47/2.71  tff(c_10900, plain, (![B_1405, A_1406]: (B_1405=A_1406 | ~r1_tarski(k1_tarski(A_1406), k1_tarski(B_1405)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.47/2.71  tff(c_10903, plain, (![B_1405]: (B_1405='#skF_8' | ~r1_tarski(k1_xboole_0, k1_tarski(B_1405)))), inference(superposition, [status(thm), theory('equality')], [c_10839, c_10900])).
% 7.47/2.71  tff(c_10918, plain, (![B_1407]: (B_1407='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_10903])).
% 7.47/2.71  tff(c_38, plain, (![C_36]: (r2_hidden(C_36, k1_tarski(C_36)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.47/2.71  tff(c_10984, plain, (![C_36]: (r2_hidden(C_36, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10918, c_38])).
% 7.47/2.71  tff(c_10914, plain, (![B_1405]: (B_1405='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_10903])).
% 7.47/2.71  tff(c_11019, plain, (![A_2580, B_2581, C_2582]: (~r1_xboole_0(A_2580, B_2581) | ~r2_hidden(C_2582, k3_xboole_0(A_2580, B_2581)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.47/2.71  tff(c_11021, plain, (![A_2580, B_2581, C_2582]: (~r1_xboole_0(A_2580, B_2581) | ~r2_hidden(C_2582, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10914, c_11019])).
% 7.47/2.71  tff(c_11030, plain, (![A_2580, B_2581]: (~r1_xboole_0(A_2580, B_2581))), inference(demodulation, [status(thm), theory('equality')], [c_10984, c_11021])).
% 7.47/2.71  tff(c_28, plain, (![A_22, C_24, B_23]: (r1_xboole_0(A_22, k4_xboole_0(C_24, B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.47/2.71  tff(c_14308, plain, (![A_22, B_23]: (~r1_tarski(A_22, B_23))), inference(negUnitSimplification, [status(thm)], [c_11030, c_28])).
% 7.47/2.71  tff(c_10756, plain, (![A_1394, B_1395]: (r1_tarski(A_1394, B_1395) | k4_xboole_0(A_1394, B_1395)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.47/2.71  tff(c_26, plain, (![A_21]: (k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.47/2.71  tff(c_10761, plain, (![A_1394]: (k1_xboole_0=A_1394 | k4_xboole_0(A_1394, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10756, c_26])).
% 7.47/2.71  tff(c_10944, plain, (![A_1394]: (k1_xboole_0=A_1394 | k1_xboole_0!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_10918, c_10761])).
% 7.47/2.71  tff(c_11044, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_10944])).
% 7.47/2.71  tff(c_11048, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_10914, c_11044])).
% 7.47/2.71  tff(c_11051, plain, (![A_2742]: (k1_xboole_0=A_2742)), inference(splitRight, [status(thm)], [c_10944])).
% 7.47/2.71  tff(c_11077, plain, (![B_54, A_53]: (B_54=A_53 | ~r1_tarski(k1_xboole_0, k1_tarski(B_54)))), inference(superposition, [status(thm), theory('equality')], [c_11051, c_62])).
% 7.47/2.71  tff(c_13771, plain, (![B_54]: (B_54='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_11077])).
% 7.47/2.71  tff(c_11114, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_10944])).
% 7.47/2.71  tff(c_10671, plain, (![A_1385, B_1386]: (r1_tarski(k4_xboole_0(A_1385, B_1386), A_1385))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.47/2.71  tff(c_10677, plain, (![B_1387]: (k4_xboole_0(k1_xboole_0, B_1387)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10671, c_26])).
% 7.47/2.71  tff(c_10682, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10677, c_24])).
% 7.47/2.71  tff(c_11115, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11114, c_10682])).
% 7.47/2.71  tff(c_13773, plain, (r1_tarski('#skF_9', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_13771, c_11115])).
% 7.47/2.71  tff(c_14319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14308, c_13773])).
% 7.47/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.71  
% 7.47/2.71  Inference rules
% 7.47/2.71  ----------------------
% 7.47/2.71  #Ref     : 1
% 7.47/2.71  #Sup     : 3415
% 7.47/2.71  #Fact    : 1
% 7.47/2.71  #Define  : 0
% 7.47/2.71  #Split   : 5
% 7.47/2.71  #Chain   : 0
% 7.47/2.71  #Close   : 0
% 7.47/2.71  
% 7.47/2.71  Ordering : KBO
% 7.47/2.71  
% 7.47/2.71  Simplification rules
% 7.47/2.71  ----------------------
% 7.47/2.71  #Subsume      : 576
% 7.47/2.71  #Demod        : 1894
% 7.47/2.71  #Tautology    : 1292
% 7.47/2.71  #SimpNegUnit  : 33
% 7.47/2.71  #BackRed      : 21
% 7.47/2.71  
% 7.47/2.71  #Partial instantiations: 1344
% 7.47/2.71  #Strategies tried      : 1
% 7.47/2.71  
% 7.47/2.71  Timing (in seconds)
% 7.47/2.71  ----------------------
% 7.76/2.72  Preprocessing        : 0.35
% 7.76/2.72  Parsing              : 0.19
% 7.76/2.72  CNF conversion       : 0.03
% 7.76/2.72  Main loop            : 1.58
% 7.76/2.72  Inferencing          : 0.50
% 7.76/2.72  Reduction            : 0.69
% 7.76/2.72  Demodulation         : 0.57
% 7.76/2.72  BG Simplification    : 0.06
% 7.76/2.72  Subsumption          : 0.24
% 7.76/2.72  Abstraction          : 0.07
% 7.76/2.72  MUC search           : 0.00
% 7.76/2.72  Cooper               : 0.00
% 7.76/2.72  Total                : 1.97
% 7.76/2.72  Index Insertion      : 0.00
% 7.76/2.72  Index Deletion       : 0.00
% 7.76/2.72  Index Matching       : 0.00
% 7.76/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
