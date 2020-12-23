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
% DateTime   : Thu Dec  3 09:48:34 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 154 expanded)
%              Number of leaves         :   33 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 216 expanded)
%              Number of equality atoms :   53 ( 110 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_10 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5

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

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_660,plain,(
    ! [A_126,B_127,C_128] :
      ( ~ r1_xboole_0(A_126,B_127)
      | ~ r2_hidden(C_128,k3_xboole_0(A_126,B_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_666,plain,(
    ! [A_129,B_130] :
      ( ~ r1_xboole_0(A_129,B_130)
      | k3_xboole_0(A_129,B_130) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_660])).

tff(c_675,plain,(
    ! [A_131] : k3_xboole_0(A_131,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_666])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_680,plain,(
    ! [A_131,C_5] :
      ( ~ r1_xboole_0(A_131,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_4])).

tff(c_688,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_680])).

tff(c_674,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_666])).

tff(c_10,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_691,plain,(
    ! [A_132,B_133] : k4_xboole_0(A_132,k4_xboole_0(A_132,B_133)) = k3_xboole_0(A_132,B_133) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_709,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_691])).

tff(c_713,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_709])).

tff(c_433,plain,(
    ! [A_89,B_90,C_91] :
      ( ~ r1_xboole_0(A_89,B_90)
      | ~ r2_hidden(C_91,k3_xboole_0(A_89,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_439,plain,(
    ! [A_92,B_93] :
      ( ~ r1_xboole_0(A_92,B_93)
      | k3_xboole_0(A_92,B_93) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_433])).

tff(c_448,plain,(
    ! [A_94] : k3_xboole_0(A_94,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_439])).

tff(c_453,plain,(
    ! [A_94,C_5] :
      ( ~ r1_xboole_0(A_94,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_4])).

tff(c_461,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_453])).

tff(c_447,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_439])).

tff(c_480,plain,(
    ! [A_97,B_98] : k4_xboole_0(A_97,k4_xboole_0(A_97,B_98)) = k3_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_501,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_480])).

tff(c_505,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_501])).

tff(c_64,plain,
    ( '#skF_7' != '#skF_8'
    | '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_70,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_159,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_165,plain,(
    ! [A_68,B_69] :
      ( ~ r1_xboole_0(A_68,B_69)
      | k3_xboole_0(A_68,B_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_159])).

tff(c_174,plain,(
    ! [A_70] : k3_xboole_0(A_70,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_165])).

tff(c_8,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_182,plain,(
    ! [A_70] : k5_xboole_0(A_70,k1_xboole_0) = k4_xboole_0(A_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_8])).

tff(c_188,plain,(
    ! [A_70] : k5_xboole_0(A_70,k1_xboole_0) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_182])).

tff(c_60,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(k1_tarski(A_36),B_37)
      | r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_299,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(k1_tarski(A_80),B_81) = k1_xboole_0
      | r2_hidden(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_60,c_165])).

tff(c_316,plain,(
    ! [A_80,B_81] :
      ( k5_xboole_0(k1_tarski(A_80),k1_xboole_0) = k4_xboole_0(k1_tarski(A_80),B_81)
      | r2_hidden(A_80,B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_8])).

tff(c_346,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(k1_tarski(A_85),B_86) = k1_tarski(A_85)
      | r2_hidden(A_85,B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_316])).

tff(c_62,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k1_tarski('#skF_7')
    | '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_158,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k1_tarski('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_386,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_158])).

tff(c_40,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_412,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_386,c_40])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_412])).

tff(c_417,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_418,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) != k1_tarski('#skF_7')
    | k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_10')) = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_428,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_418,c_66])).

tff(c_506,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_428])).

tff(c_42,plain,(
    ! [C_25] : r2_hidden(C_25,k1_tarski(C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_540,plain,(
    r2_hidden('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_42])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_540])).

tff(c_547,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_546,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( '#skF_7' != '#skF_8'
    | k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_10')) = k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_552,plain,
    ( '#skF_7' != '#skF_8'
    | k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_68])).

tff(c_553,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_552])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_553])).

tff(c_560,plain,(
    k4_xboole_0(k1_tarski('#skF_9'),k1_tarski('#skF_9')) = k1_tarski('#skF_9') ),
    inference(splitRight,[status(thm)],[c_552])).

tff(c_721,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_560])).

tff(c_755,plain,(
    r2_hidden('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_42])).

tff(c_760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_688,c_755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:11:37 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.46  
% 2.32/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.46  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_10 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 2.77/1.46  
% 2.77/1.46  %Foreground sorts:
% 2.77/1.46  
% 2.77/1.46  
% 2.77/1.46  %Background operators:
% 2.77/1.46  
% 2.77/1.46  
% 2.77/1.46  %Foreground operators:
% 2.77/1.46  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.77/1.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.77/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.77/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.77/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.46  tff('#skF_10', type, '#skF_10': $i).
% 2.77/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.46  tff('#skF_9', type, '#skF_9': $i).
% 2.77/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.77/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.77/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.77/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.46  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.77/1.46  
% 2.77/1.48  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.77/1.48  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.77/1.48  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.77/1.48  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.77/1.48  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.77/1.48  tff(f_96, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.77/1.48  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.77/1.48  tff(f_90, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.77/1.48  tff(f_77, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.77/1.48  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.77/1.48  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.48  tff(c_660, plain, (![A_126, B_127, C_128]: (~r1_xboole_0(A_126, B_127) | ~r2_hidden(C_128, k3_xboole_0(A_126, B_127)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.48  tff(c_666, plain, (![A_129, B_130]: (~r1_xboole_0(A_129, B_130) | k3_xboole_0(A_129, B_130)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_660])).
% 2.77/1.48  tff(c_675, plain, (![A_131]: (k3_xboole_0(A_131, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_666])).
% 2.77/1.48  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.48  tff(c_680, plain, (![A_131, C_5]: (~r1_xboole_0(A_131, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_675, c_4])).
% 2.77/1.48  tff(c_688, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_680])).
% 2.77/1.48  tff(c_674, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_666])).
% 2.77/1.48  tff(c_10, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.77/1.48  tff(c_691, plain, (![A_132, B_133]: (k4_xboole_0(A_132, k4_xboole_0(A_132, B_133))=k3_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.77/1.48  tff(c_709, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_691])).
% 2.77/1.48  tff(c_713, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_674, c_709])).
% 2.77/1.48  tff(c_433, plain, (![A_89, B_90, C_91]: (~r1_xboole_0(A_89, B_90) | ~r2_hidden(C_91, k3_xboole_0(A_89, B_90)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.48  tff(c_439, plain, (![A_92, B_93]: (~r1_xboole_0(A_92, B_93) | k3_xboole_0(A_92, B_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_433])).
% 2.77/1.48  tff(c_448, plain, (![A_94]: (k3_xboole_0(A_94, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_439])).
% 2.77/1.48  tff(c_453, plain, (![A_94, C_5]: (~r1_xboole_0(A_94, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_448, c_4])).
% 2.77/1.48  tff(c_461, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_453])).
% 2.77/1.48  tff(c_447, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_439])).
% 2.77/1.48  tff(c_480, plain, (![A_97, B_98]: (k4_xboole_0(A_97, k4_xboole_0(A_97, B_98))=k3_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.77/1.48  tff(c_501, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_480])).
% 2.77/1.48  tff(c_505, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_447, c_501])).
% 2.77/1.48  tff(c_64, plain, ('#skF_7'!='#skF_8' | '#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.77/1.48  tff(c_70, plain, ('#skF_7'!='#skF_8'), inference(splitLeft, [status(thm)], [c_64])).
% 2.77/1.48  tff(c_159, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.48  tff(c_165, plain, (![A_68, B_69]: (~r1_xboole_0(A_68, B_69) | k3_xboole_0(A_68, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_159])).
% 2.77/1.48  tff(c_174, plain, (![A_70]: (k3_xboole_0(A_70, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_165])).
% 2.77/1.48  tff(c_8, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.48  tff(c_182, plain, (![A_70]: (k5_xboole_0(A_70, k1_xboole_0)=k4_xboole_0(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_174, c_8])).
% 2.77/1.48  tff(c_188, plain, (![A_70]: (k5_xboole_0(A_70, k1_xboole_0)=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_182])).
% 2.77/1.48  tff(c_60, plain, (![A_36, B_37]: (r1_xboole_0(k1_tarski(A_36), B_37) | r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.77/1.48  tff(c_299, plain, (![A_80, B_81]: (k3_xboole_0(k1_tarski(A_80), B_81)=k1_xboole_0 | r2_hidden(A_80, B_81))), inference(resolution, [status(thm)], [c_60, c_165])).
% 2.77/1.48  tff(c_316, plain, (![A_80, B_81]: (k5_xboole_0(k1_tarski(A_80), k1_xboole_0)=k4_xboole_0(k1_tarski(A_80), B_81) | r2_hidden(A_80, B_81))), inference(superposition, [status(thm), theory('equality')], [c_299, c_8])).
% 2.77/1.48  tff(c_346, plain, (![A_85, B_86]: (k4_xboole_0(k1_tarski(A_85), B_86)=k1_tarski(A_85) | r2_hidden(A_85, B_86))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_316])).
% 2.77/1.48  tff(c_62, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k1_tarski('#skF_7') | '#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.77/1.48  tff(c_158, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k1_tarski('#skF_7')), inference(splitLeft, [status(thm)], [c_62])).
% 2.77/1.48  tff(c_386, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_346, c_158])).
% 2.77/1.48  tff(c_40, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.48  tff(c_412, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_386, c_40])).
% 2.77/1.48  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_412])).
% 2.77/1.48  tff(c_417, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_62])).
% 2.77/1.48  tff(c_418, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 2.77/1.48  tff(c_66, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))!=k1_tarski('#skF_7') | k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_10'))=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.77/1.48  tff(c_428, plain, (k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_417, c_418, c_66])).
% 2.77/1.48  tff(c_506, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_505, c_428])).
% 2.77/1.48  tff(c_42, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(C_25)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.48  tff(c_540, plain, (r2_hidden('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_506, c_42])).
% 2.77/1.48  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_461, c_540])).
% 2.77/1.48  tff(c_547, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_64])).
% 2.77/1.48  tff(c_546, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_64])).
% 2.77/1.48  tff(c_68, plain, ('#skF_7'!='#skF_8' | k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_10'))=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.77/1.48  tff(c_552, plain, ('#skF_7'!='#skF_8' | k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_68])).
% 2.77/1.48  tff(c_553, plain, ('#skF_7'!='#skF_8'), inference(splitLeft, [status(thm)], [c_552])).
% 2.77/1.48  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_547, c_553])).
% 2.77/1.48  tff(c_560, plain, (k4_xboole_0(k1_tarski('#skF_9'), k1_tarski('#skF_9'))=k1_tarski('#skF_9')), inference(splitRight, [status(thm)], [c_552])).
% 2.77/1.48  tff(c_721, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_713, c_560])).
% 2.77/1.48  tff(c_755, plain, (r2_hidden('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_721, c_42])).
% 2.77/1.48  tff(c_760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_688, c_755])).
% 2.77/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.48  
% 2.77/1.48  Inference rules
% 2.77/1.48  ----------------------
% 2.77/1.48  #Ref     : 0
% 2.77/1.48  #Sup     : 160
% 2.77/1.48  #Fact    : 0
% 2.77/1.48  #Define  : 0
% 2.77/1.48  #Split   : 3
% 2.77/1.48  #Chain   : 0
% 2.77/1.48  #Close   : 0
% 2.77/1.48  
% 2.77/1.48  Ordering : KBO
% 2.77/1.48  
% 2.77/1.48  Simplification rules
% 2.77/1.48  ----------------------
% 2.77/1.48  #Subsume      : 8
% 2.77/1.48  #Demod        : 47
% 2.77/1.48  #Tautology    : 107
% 2.77/1.48  #SimpNegUnit  : 9
% 2.77/1.48  #BackRed      : 2
% 2.77/1.48  
% 2.77/1.48  #Partial instantiations: 0
% 2.77/1.48  #Strategies tried      : 1
% 2.77/1.48  
% 2.77/1.48  Timing (in seconds)
% 2.77/1.48  ----------------------
% 2.77/1.48  Preprocessing        : 0.36
% 2.77/1.48  Parsing              : 0.18
% 2.77/1.48  CNF conversion       : 0.03
% 2.77/1.48  Main loop            : 0.28
% 2.77/1.48  Inferencing          : 0.10
% 2.77/1.48  Reduction            : 0.09
% 2.77/1.48  Demodulation         : 0.06
% 2.77/1.48  BG Simplification    : 0.02
% 2.77/1.48  Subsumption          : 0.04
% 2.77/1.48  Abstraction          : 0.02
% 2.77/1.48  MUC search           : 0.00
% 2.77/1.48  Cooper               : 0.00
% 2.77/1.48  Total                : 0.68
% 2.77/1.48  Index Insertion      : 0.00
% 2.77/1.49  Index Deletion       : 0.00
% 2.77/1.49  Index Matching       : 0.00
% 2.77/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
