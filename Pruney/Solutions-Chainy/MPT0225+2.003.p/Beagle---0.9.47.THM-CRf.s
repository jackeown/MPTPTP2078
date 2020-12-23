%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:31 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 131 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 183 expanded)
%              Number of equality atoms :   42 (  83 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_10 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_26,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1985,plain,(
    ! [B_223,A_224] :
      ( r1_xboole_0(B_223,A_224)
      | ~ r1_xboole_0(A_224,B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1991,plain,(
    ! [A_19] : r1_xboole_0(k1_xboole_0,A_19) ),
    inference(resolution,[status(thm)],[c_26,c_1985])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2258,plain,(
    ! [A_262,B_263,C_264] :
      ( ~ r1_xboole_0(A_262,B_263)
      | ~ r2_hidden(C_264,k3_xboole_0(A_262,B_263)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2346,plain,(
    ! [A_273,B_274] :
      ( ~ r1_xboole_0(A_273,B_274)
      | k3_xboole_0(A_273,B_274) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_2258])).

tff(c_2379,plain,(
    ! [A_275] : k3_xboole_0(k1_xboole_0,A_275) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1991,c_2346])).

tff(c_8,plain,(
    ! [A_5,B_6,C_9] :
      ( ~ r1_xboole_0(A_5,B_6)
      | ~ r2_hidden(C_9,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2384,plain,(
    ! [A_275,C_9] :
      ( ~ r1_xboole_0(k1_xboole_0,A_275)
      | ~ r2_hidden(C_9,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2379,c_8])).

tff(c_2403,plain,(
    ! [C_9] : ~ r2_hidden(C_9,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1991,c_2384])).

tff(c_16,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2211,plain,(
    ! [A_259,B_260] :
      ( k4_xboole_0(A_259,B_260) = k1_xboole_0
      | ~ r1_tarski(A_259,B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2219,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_2211])).

tff(c_1376,plain,(
    ! [B_160,A_161] :
      ( r1_xboole_0(B_160,A_161)
      | ~ r1_xboole_0(A_161,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1382,plain,(
    ! [A_19] : r1_xboole_0(k1_xboole_0,A_19) ),
    inference(resolution,[status(thm)],[c_26,c_1376])).

tff(c_1874,plain,(
    ! [A_213,B_214,C_215] :
      ( ~ r1_xboole_0(A_213,B_214)
      | ~ r2_hidden(C_215,k3_xboole_0(A_213,B_214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1886,plain,(
    ! [A_216,B_217] :
      ( ~ r1_xboole_0(A_216,B_217)
      | k3_xboole_0(A_216,B_217) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_1874])).

tff(c_1927,plain,(
    ! [A_218] : k3_xboole_0(k1_xboole_0,A_218) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1382,c_1886])).

tff(c_1932,plain,(
    ! [A_218,C_9] :
      ( ~ r1_xboole_0(k1_xboole_0,A_218)
      | ~ r2_hidden(C_9,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1927,c_8])).

tff(c_1954,plain,(
    ! [C_9] : ~ r2_hidden(C_9,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1382,c_1932])).

tff(c_1604,plain,(
    ! [A_195,B_196] :
      ( k4_xboole_0(A_195,B_196) = k1_xboole_0
      | ~ r1_tarski(A_195,B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1612,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_1604])).

tff(c_82,plain,
    ( '#skF_7' != '#skF_8'
    | '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_99,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_219,plain,(
    ! [A_84,B_85] :
      ( r1_xboole_0(k1_tarski(A_84),B_85)
      | r2_hidden(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_394,plain,(
    ! [B_99,A_100] :
      ( r1_xboole_0(B_99,k1_tarski(A_100))
      | r2_hidden(A_100,B_99) ) ),
    inference(resolution,[status(thm)],[c_219,c_4])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1288,plain,(
    ! [B_158,A_159] :
      ( k4_xboole_0(B_158,k1_tarski(A_159)) = B_158
      | r2_hidden(A_159,B_158) ) ),
    inference(resolution,[status(thm)],[c_394,c_30])).

tff(c_80,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k1_tarski('#skF_7')
    | '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_121,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k1_tarski('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_1354,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1288,c_121])).

tff(c_58,plain,(
    ! [C_35,A_31] :
      ( C_35 = A_31
      | ~ r2_hidden(C_35,k1_tarski(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1365,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1354,c_58])).

tff(c_1369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_1365])).

tff(c_1371,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1370,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_84,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k1_tarski('#skF_7')
    | k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_10')) = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1474,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k1_tarski('#skF_7')
    | k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1370,c_84])).

tff(c_1475,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k1_tarski('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1474])).

tff(c_1601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1371,c_1475])).

tff(c_1602,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k1_tarski('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1474])).

tff(c_1701,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_1602])).

tff(c_60,plain,(
    ! [C_35] : r2_hidden(C_35,k1_tarski(C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1711,plain,(
    r2_hidden('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1701,c_60])).

tff(c_1958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1954,c_1711])).

tff(c_1959,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1960,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_86,plain,
    ( '#skF_7' != '#skF_8'
    | k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_10')) = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2055,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1959,c_1960,c_86])).

tff(c_2220,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2219,c_2055])).

tff(c_2281,plain,(
    r2_hidden('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2220,c_60])).

tff(c_2425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2403,c_2281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:43:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.58  
% 3.53/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_10 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 3.53/1.58  
% 3.53/1.58  %Foreground sorts:
% 3.53/1.58  
% 3.53/1.58  
% 3.53/1.58  %Background operators:
% 3.53/1.58  
% 3.53/1.58  
% 3.53/1.58  %Foreground operators:
% 3.53/1.58  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.53/1.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.53/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.53/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.53/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.53/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.58  tff('#skF_10', type, '#skF_10': $i).
% 3.53/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.53/1.58  tff('#skF_9', type, '#skF_9': $i).
% 3.53/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.53/1.58  tff('#skF_8', type, '#skF_8': $i).
% 3.53/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.53/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.53/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.53/1.58  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.53/1.58  
% 3.53/1.59  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.53/1.59  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.53/1.59  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.53/1.59  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.53/1.59  tff(f_59, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.59  tff(f_63, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.53/1.59  tff(f_116, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.53/1.59  tff(f_110, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.53/1.59  tff(f_75, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.53/1.59  tff(f_97, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.53/1.59  tff(c_26, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.53/1.59  tff(c_1985, plain, (![B_223, A_224]: (r1_xboole_0(B_223, A_224) | ~r1_xboole_0(A_224, B_223))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.59  tff(c_1991, plain, (![A_19]: (r1_xboole_0(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_26, c_1985])).
% 3.53/1.59  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.53/1.59  tff(c_2258, plain, (![A_262, B_263, C_264]: (~r1_xboole_0(A_262, B_263) | ~r2_hidden(C_264, k3_xboole_0(A_262, B_263)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.53/1.59  tff(c_2346, plain, (![A_273, B_274]: (~r1_xboole_0(A_273, B_274) | k3_xboole_0(A_273, B_274)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_2258])).
% 3.53/1.59  tff(c_2379, plain, (![A_275]: (k3_xboole_0(k1_xboole_0, A_275)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1991, c_2346])).
% 3.53/1.59  tff(c_8, plain, (![A_5, B_6, C_9]: (~r1_xboole_0(A_5, B_6) | ~r2_hidden(C_9, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.53/1.59  tff(c_2384, plain, (![A_275, C_9]: (~r1_xboole_0(k1_xboole_0, A_275) | ~r2_hidden(C_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2379, c_8])).
% 3.53/1.59  tff(c_2403, plain, (![C_9]: (~r2_hidden(C_9, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1991, c_2384])).
% 3.53/1.59  tff(c_16, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.53/1.59  tff(c_2211, plain, (![A_259, B_260]: (k4_xboole_0(A_259, B_260)=k1_xboole_0 | ~r1_tarski(A_259, B_260))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.53/1.59  tff(c_2219, plain, (![B_13]: (k4_xboole_0(B_13, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_2211])).
% 3.53/1.59  tff(c_1376, plain, (![B_160, A_161]: (r1_xboole_0(B_160, A_161) | ~r1_xboole_0(A_161, B_160))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.59  tff(c_1382, plain, (![A_19]: (r1_xboole_0(k1_xboole_0, A_19))), inference(resolution, [status(thm)], [c_26, c_1376])).
% 3.53/1.59  tff(c_1874, plain, (![A_213, B_214, C_215]: (~r1_xboole_0(A_213, B_214) | ~r2_hidden(C_215, k3_xboole_0(A_213, B_214)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.53/1.59  tff(c_1886, plain, (![A_216, B_217]: (~r1_xboole_0(A_216, B_217) | k3_xboole_0(A_216, B_217)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1874])).
% 3.53/1.59  tff(c_1927, plain, (![A_218]: (k3_xboole_0(k1_xboole_0, A_218)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1382, c_1886])).
% 3.53/1.59  tff(c_1932, plain, (![A_218, C_9]: (~r1_xboole_0(k1_xboole_0, A_218) | ~r2_hidden(C_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1927, c_8])).
% 3.53/1.59  tff(c_1954, plain, (![C_9]: (~r2_hidden(C_9, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1382, c_1932])).
% 3.53/1.59  tff(c_1604, plain, (![A_195, B_196]: (k4_xboole_0(A_195, B_196)=k1_xboole_0 | ~r1_tarski(A_195, B_196))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.53/1.59  tff(c_1612, plain, (![B_13]: (k4_xboole_0(B_13, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1604])).
% 3.53/1.59  tff(c_82, plain, ('#skF_7'!='#skF_8' | '#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.59  tff(c_99, plain, ('#skF_7'!='#skF_8'), inference(splitLeft, [status(thm)], [c_82])).
% 3.53/1.59  tff(c_219, plain, (![A_84, B_85]: (r1_xboole_0(k1_tarski(A_84), B_85) | r2_hidden(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.53/1.59  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.59  tff(c_394, plain, (![B_99, A_100]: (r1_xboole_0(B_99, k1_tarski(A_100)) | r2_hidden(A_100, B_99))), inference(resolution, [status(thm)], [c_219, c_4])).
% 3.53/1.59  tff(c_30, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.53/1.59  tff(c_1288, plain, (![B_158, A_159]: (k4_xboole_0(B_158, k1_tarski(A_159))=B_158 | r2_hidden(A_159, B_158))), inference(resolution, [status(thm)], [c_394, c_30])).
% 3.53/1.59  tff(c_80, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k1_tarski('#skF_7') | '#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.59  tff(c_121, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k1_tarski('#skF_7')), inference(splitLeft, [status(thm)], [c_80])).
% 3.53/1.59  tff(c_1354, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1288, c_121])).
% 3.53/1.59  tff(c_58, plain, (![C_35, A_31]: (C_35=A_31 | ~r2_hidden(C_35, k1_tarski(A_31)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.53/1.59  tff(c_1365, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_1354, c_58])).
% 3.53/1.59  tff(c_1369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_1365])).
% 3.53/1.59  tff(c_1371, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_80])).
% 3.53/1.59  tff(c_1370, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_80])).
% 3.53/1.59  tff(c_84, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k1_tarski('#skF_7') | k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_10'))=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.59  tff(c_1474, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k1_tarski('#skF_7') | k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1370, c_84])).
% 3.53/1.59  tff(c_1475, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k1_tarski('#skF_7')), inference(splitLeft, [status(thm)], [c_1474])).
% 3.53/1.59  tff(c_1601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1371, c_1475])).
% 3.53/1.59  tff(c_1602, plain, (k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k1_tarski('#skF_9')), inference(splitRight, [status(thm)], [c_1474])).
% 3.53/1.59  tff(c_1701, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_1602])).
% 3.53/1.59  tff(c_60, plain, (![C_35]: (r2_hidden(C_35, k1_tarski(C_35)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.53/1.59  tff(c_1711, plain, (r2_hidden('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1701, c_60])).
% 3.53/1.59  tff(c_1958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1954, c_1711])).
% 3.53/1.59  tff(c_1959, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_82])).
% 3.53/1.59  tff(c_1960, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_82])).
% 3.53/1.59  tff(c_86, plain, ('#skF_7'!='#skF_8' | k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_10'))=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.59  tff(c_2055, plain, (k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1959, c_1960, c_86])).
% 3.53/1.59  tff(c_2220, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2219, c_2055])).
% 3.53/1.59  tff(c_2281, plain, (r2_hidden('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2220, c_60])).
% 3.53/1.59  tff(c_2425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2403, c_2281])).
% 3.53/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.59  
% 3.53/1.59  Inference rules
% 3.53/1.59  ----------------------
% 3.53/1.59  #Ref     : 0
% 3.53/1.59  #Sup     : 548
% 3.53/1.59  #Fact    : 0
% 3.53/1.59  #Define  : 0
% 3.53/1.59  #Split   : 4
% 3.53/1.59  #Chain   : 0
% 3.53/1.59  #Close   : 0
% 3.53/1.59  
% 3.53/1.59  Ordering : KBO
% 3.53/1.59  
% 3.53/1.59  Simplification rules
% 3.53/1.59  ----------------------
% 3.53/1.59  #Subsume      : 47
% 3.53/1.59  #Demod        : 215
% 3.53/1.59  #Tautology    : 361
% 3.53/1.59  #SimpNegUnit  : 17
% 3.53/1.59  #BackRed      : 4
% 3.53/1.59  
% 3.53/1.59  #Partial instantiations: 0
% 3.53/1.59  #Strategies tried      : 1
% 3.53/1.59  
% 3.53/1.59  Timing (in seconds)
% 3.53/1.59  ----------------------
% 3.53/1.60  Preprocessing        : 0.34
% 3.53/1.60  Parsing              : 0.17
% 3.53/1.60  CNF conversion       : 0.03
% 3.53/1.60  Main loop            : 0.51
% 3.53/1.60  Inferencing          : 0.18
% 3.53/1.60  Reduction            : 0.17
% 3.53/1.60  Demodulation         : 0.12
% 3.53/1.60  BG Simplification    : 0.03
% 3.53/1.60  Subsumption          : 0.08
% 3.53/1.60  Abstraction          : 0.03
% 3.53/1.60  MUC search           : 0.00
% 3.53/1.60  Cooper               : 0.00
% 3.53/1.60  Total                : 0.88
% 3.53/1.60  Index Insertion      : 0.00
% 3.53/1.60  Index Deletion       : 0.00
% 3.53/1.60  Index Matching       : 0.00
% 3.53/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
