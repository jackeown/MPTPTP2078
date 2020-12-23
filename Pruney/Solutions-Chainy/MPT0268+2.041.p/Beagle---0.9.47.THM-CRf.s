%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:39 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 136 expanded)
%              Number of leaves         :   38 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 207 expanded)
%              Number of equality atoms :   47 (  86 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_92,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_94,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_108,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_133,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_64,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_54,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_182,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k1_xboole_0
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_186,plain,(
    ! [B_17] : k4_xboole_0(B_17,B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_182])).

tff(c_259,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_280,plain,(
    ! [A_24] : k4_xboole_0(A_24,A_24) = k3_xboole_0(A_24,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_259])).

tff(c_285,plain,(
    ! [A_97] : k3_xboole_0(A_97,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_280])).

tff(c_60,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_293,plain,(
    ! [A_97] : k5_xboole_0(A_97,k1_xboole_0) = k4_xboole_0(A_97,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_60])).

tff(c_308,plain,(
    ! [A_97] : k5_xboole_0(A_97,k1_xboole_0) = A_97 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_293])).

tff(c_2122,plain,(
    ! [A_216,B_217,C_218] :
      ( r2_hidden('#skF_3'(A_216,B_217,C_218),A_216)
      | r2_hidden('#skF_4'(A_216,B_217,C_218),C_218)
      | k4_xboole_0(A_216,B_217) = C_218 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8,C_9),B_8)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2127,plain,(
    ! [A_216,C_218] :
      ( r2_hidden('#skF_4'(A_216,A_216,C_218),C_218)
      | k4_xboole_0(A_216,A_216) = C_218 ) ),
    inference(resolution,[status(thm)],[c_2122,c_34])).

tff(c_2299,plain,(
    ! [A_219,C_220] :
      ( r2_hidden('#skF_4'(A_219,A_219,C_220),C_220)
      | k1_xboole_0 = C_220 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_2127])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2392,plain,(
    ! [A_219,A_1,B_2] :
      ( r2_hidden('#skF_4'(A_219,A_219,k3_xboole_0(A_1,B_2)),B_2)
      | k3_xboole_0(A_1,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2299,c_4])).

tff(c_104,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(k1_tarski(A_46),B_47)
      | r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_214,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,B_80) = A_79
      | ~ r1_xboole_0(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_374,plain,(
    ! [A_111,B_112] :
      ( k4_xboole_0(k1_tarski(A_111),B_112) = k1_tarski(A_111)
      | r2_hidden(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_104,c_214])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_383,plain,(
    ! [D_12,B_112,A_111] :
      ( ~ r2_hidden(D_12,B_112)
      | ~ r2_hidden(D_12,k1_tarski(A_111))
      | r2_hidden(A_111,B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_22])).

tff(c_5837,plain,(
    ! [A_354,C_355,A_356] :
      ( ~ r2_hidden('#skF_4'(A_354,A_354,C_355),k1_tarski(A_356))
      | r2_hidden(A_356,C_355)
      | k1_xboole_0 = C_355 ) ),
    inference(resolution,[status(thm)],[c_2299,c_383])).

tff(c_5883,plain,(
    ! [A_357,A_358] :
      ( r2_hidden(A_357,k3_xboole_0(A_358,k1_tarski(A_357)))
      | k3_xboole_0(A_358,k1_tarski(A_357)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2392,c_5837])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6136,plain,(
    ! [A_361,A_362] :
      ( r2_hidden(A_361,A_362)
      | k3_xboole_0(A_362,k1_tarski(A_361)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5883,c_6])).

tff(c_6203,plain,(
    ! [A_362,A_361] :
      ( k4_xboole_0(A_362,k1_tarski(A_361)) = k5_xboole_0(A_362,k1_xboole_0)
      | r2_hidden(A_361,A_362) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6136,c_60])).

tff(c_6260,plain,(
    ! [A_363,A_364] :
      ( k4_xboole_0(A_363,k1_tarski(A_364)) = A_363
      | r2_hidden(A_364,A_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_6203])).

tff(c_106,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_155,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_6350,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6260,c_155])).

tff(c_6402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_6350])).

tff(c_6403,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_96,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_137,plain,(
    ! [A_60,B_61] : k1_enumset1(A_60,A_60,B_61) = k2_tarski(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_74,plain,(
    ! [E_35,A_29,B_30] : r2_hidden(E_35,k1_enumset1(A_29,B_30,E_35)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6409,plain,(
    ! [B_365,A_366] : r2_hidden(B_365,k2_tarski(A_366,B_365)) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_74])).

tff(c_6412,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_6409])).

tff(c_6404,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_110,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6449,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6404,c_110])).

tff(c_6589,plain,(
    ! [D_391,B_392,A_393] :
      ( ~ r2_hidden(D_391,B_392)
      | ~ r2_hidden(D_391,k4_xboole_0(A_393,B_392)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6606,plain,(
    ! [D_396] :
      ( ~ r2_hidden(D_396,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_396,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6449,c_6589])).

tff(c_6610,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_6412,c_6606])).

tff(c_6614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6403,c_6610])).

tff(c_6615,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_6646,plain,(
    ! [A_415,B_416] : k1_enumset1(A_415,A_415,B_416) = k2_tarski(A_415,B_416) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_76,plain,(
    ! [E_35,A_29,C_31] : r2_hidden(E_35,k1_enumset1(A_29,E_35,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6664,plain,(
    ! [A_417,B_418] : r2_hidden(A_417,k2_tarski(A_417,B_418)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6646,c_76])).

tff(c_6667,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_6664])).

tff(c_6616,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_112,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6670,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6616,c_112])).

tff(c_6712,plain,(
    ! [D_427,B_428,A_429] :
      ( ~ r2_hidden(D_427,B_428)
      | ~ r2_hidden(D_427,k4_xboole_0(A_429,B_428)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6723,plain,(
    ! [D_432] :
      ( ~ r2_hidden(D_432,k1_tarski('#skF_10'))
      | ~ r2_hidden(D_432,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6670,c_6712])).

tff(c_6727,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_6667,c_6723])).

tff(c_6731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6615,c_6727])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:13:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.84/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.13  
% 5.84/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.13  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 5.84/2.13  
% 5.84/2.13  %Foreground sorts:
% 5.84/2.13  
% 5.84/2.13  
% 5.84/2.13  %Background operators:
% 5.84/2.13  
% 5.84/2.13  
% 5.84/2.13  %Foreground operators:
% 5.84/2.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.84/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.84/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.84/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.84/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.84/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.84/2.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.84/2.13  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.84/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.84/2.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.84/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.84/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.84/2.13  tff('#skF_10', type, '#skF_10': $i).
% 5.84/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.84/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.84/2.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.84/2.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.84/2.13  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 5.84/2.13  tff('#skF_9', type, '#skF_9': $i).
% 5.84/2.13  tff('#skF_8', type, '#skF_8': $i).
% 5.84/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.84/2.13  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.84/2.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.84/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.84/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.84/2.13  
% 5.84/2.15  tff(f_109, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.84/2.15  tff(f_69, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.84/2.15  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.84/2.15  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.84/2.15  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.84/2.15  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.84/2.15  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.84/2.15  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.84/2.15  tff(f_103, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.84/2.15  tff(f_75, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.84/2.15  tff(f_92, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.84/2.15  tff(f_94, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.84/2.15  tff(f_90, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.84/2.15  tff(c_108, plain, (~r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.84/2.15  tff(c_133, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_108])).
% 5.84/2.15  tff(c_64, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.84/2.15  tff(c_54, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.84/2.15  tff(c_182, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k1_xboole_0 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.84/2.15  tff(c_186, plain, (![B_17]: (k4_xboole_0(B_17, B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_182])).
% 5.84/2.15  tff(c_259, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k4_xboole_0(A_95, B_96))=k3_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.84/2.15  tff(c_280, plain, (![A_24]: (k4_xboole_0(A_24, A_24)=k3_xboole_0(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_64, c_259])).
% 5.84/2.15  tff(c_285, plain, (![A_97]: (k3_xboole_0(A_97, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_280])).
% 5.84/2.15  tff(c_60, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.84/2.15  tff(c_293, plain, (![A_97]: (k5_xboole_0(A_97, k1_xboole_0)=k4_xboole_0(A_97, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_285, c_60])).
% 5.84/2.15  tff(c_308, plain, (![A_97]: (k5_xboole_0(A_97, k1_xboole_0)=A_97)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_293])).
% 5.84/2.15  tff(c_2122, plain, (![A_216, B_217, C_218]: (r2_hidden('#skF_3'(A_216, B_217, C_218), A_216) | r2_hidden('#skF_4'(A_216, B_217, C_218), C_218) | k4_xboole_0(A_216, B_217)=C_218)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.84/2.15  tff(c_34, plain, (![A_7, B_8, C_9]: (~r2_hidden('#skF_3'(A_7, B_8, C_9), B_8) | r2_hidden('#skF_4'(A_7, B_8, C_9), C_9) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.84/2.15  tff(c_2127, plain, (![A_216, C_218]: (r2_hidden('#skF_4'(A_216, A_216, C_218), C_218) | k4_xboole_0(A_216, A_216)=C_218)), inference(resolution, [status(thm)], [c_2122, c_34])).
% 5.84/2.15  tff(c_2299, plain, (![A_219, C_220]: (r2_hidden('#skF_4'(A_219, A_219, C_220), C_220) | k1_xboole_0=C_220)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_2127])).
% 5.84/2.15  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.84/2.15  tff(c_2392, plain, (![A_219, A_1, B_2]: (r2_hidden('#skF_4'(A_219, A_219, k3_xboole_0(A_1, B_2)), B_2) | k3_xboole_0(A_1, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2299, c_4])).
% 5.84/2.15  tff(c_104, plain, (![A_46, B_47]: (r1_xboole_0(k1_tarski(A_46), B_47) | r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.84/2.15  tff(c_214, plain, (![A_79, B_80]: (k4_xboole_0(A_79, B_80)=A_79 | ~r1_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.84/2.15  tff(c_374, plain, (![A_111, B_112]: (k4_xboole_0(k1_tarski(A_111), B_112)=k1_tarski(A_111) | r2_hidden(A_111, B_112))), inference(resolution, [status(thm)], [c_104, c_214])).
% 5.84/2.15  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.84/2.15  tff(c_383, plain, (![D_12, B_112, A_111]: (~r2_hidden(D_12, B_112) | ~r2_hidden(D_12, k1_tarski(A_111)) | r2_hidden(A_111, B_112))), inference(superposition, [status(thm), theory('equality')], [c_374, c_22])).
% 5.84/2.15  tff(c_5837, plain, (![A_354, C_355, A_356]: (~r2_hidden('#skF_4'(A_354, A_354, C_355), k1_tarski(A_356)) | r2_hidden(A_356, C_355) | k1_xboole_0=C_355)), inference(resolution, [status(thm)], [c_2299, c_383])).
% 5.84/2.15  tff(c_5883, plain, (![A_357, A_358]: (r2_hidden(A_357, k3_xboole_0(A_358, k1_tarski(A_357))) | k3_xboole_0(A_358, k1_tarski(A_357))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2392, c_5837])).
% 5.84/2.15  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.84/2.15  tff(c_6136, plain, (![A_361, A_362]: (r2_hidden(A_361, A_362) | k3_xboole_0(A_362, k1_tarski(A_361))=k1_xboole_0)), inference(resolution, [status(thm)], [c_5883, c_6])).
% 5.84/2.15  tff(c_6203, plain, (![A_362, A_361]: (k4_xboole_0(A_362, k1_tarski(A_361))=k5_xboole_0(A_362, k1_xboole_0) | r2_hidden(A_361, A_362))), inference(superposition, [status(thm), theory('equality')], [c_6136, c_60])).
% 5.84/2.15  tff(c_6260, plain, (![A_363, A_364]: (k4_xboole_0(A_363, k1_tarski(A_364))=A_363 | r2_hidden(A_364, A_363))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_6203])).
% 5.84/2.15  tff(c_106, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.84/2.15  tff(c_155, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_106])).
% 5.84/2.15  tff(c_6350, plain, (r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6260, c_155])).
% 5.84/2.15  tff(c_6402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_6350])).
% 5.84/2.15  tff(c_6403, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_106])).
% 5.84/2.15  tff(c_96, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.84/2.15  tff(c_137, plain, (![A_60, B_61]: (k1_enumset1(A_60, A_60, B_61)=k2_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.84/2.15  tff(c_74, plain, (![E_35, A_29, B_30]: (r2_hidden(E_35, k1_enumset1(A_29, B_30, E_35)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.84/2.15  tff(c_6409, plain, (![B_365, A_366]: (r2_hidden(B_365, k2_tarski(A_366, B_365)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_74])).
% 5.84/2.15  tff(c_6412, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_6409])).
% 5.84/2.15  tff(c_6404, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_106])).
% 5.84/2.15  tff(c_110, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.84/2.15  tff(c_6449, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6404, c_110])).
% 5.84/2.15  tff(c_6589, plain, (![D_391, B_392, A_393]: (~r2_hidden(D_391, B_392) | ~r2_hidden(D_391, k4_xboole_0(A_393, B_392)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.84/2.15  tff(c_6606, plain, (![D_396]: (~r2_hidden(D_396, k1_tarski('#skF_10')) | ~r2_hidden(D_396, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6449, c_6589])).
% 5.84/2.15  tff(c_6610, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_6412, c_6606])).
% 5.84/2.15  tff(c_6614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6403, c_6610])).
% 5.84/2.15  tff(c_6615, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_108])).
% 5.84/2.15  tff(c_6646, plain, (![A_415, B_416]: (k1_enumset1(A_415, A_415, B_416)=k2_tarski(A_415, B_416))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.84/2.15  tff(c_76, plain, (![E_35, A_29, C_31]: (r2_hidden(E_35, k1_enumset1(A_29, E_35, C_31)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.84/2.15  tff(c_6664, plain, (![A_417, B_418]: (r2_hidden(A_417, k2_tarski(A_417, B_418)))), inference(superposition, [status(thm), theory('equality')], [c_6646, c_76])).
% 5.84/2.15  tff(c_6667, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_6664])).
% 5.84/2.15  tff(c_6616, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_108])).
% 5.84/2.15  tff(c_112, plain, (~r2_hidden('#skF_8', '#skF_7') | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.84/2.15  tff(c_6670, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6616, c_112])).
% 5.84/2.15  tff(c_6712, plain, (![D_427, B_428, A_429]: (~r2_hidden(D_427, B_428) | ~r2_hidden(D_427, k4_xboole_0(A_429, B_428)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.84/2.15  tff(c_6723, plain, (![D_432]: (~r2_hidden(D_432, k1_tarski('#skF_10')) | ~r2_hidden(D_432, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6670, c_6712])).
% 5.84/2.15  tff(c_6727, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_6667, c_6723])).
% 5.84/2.15  tff(c_6731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6615, c_6727])).
% 5.84/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.15  
% 5.84/2.15  Inference rules
% 5.84/2.15  ----------------------
% 5.84/2.15  #Ref     : 0
% 5.84/2.15  #Sup     : 1513
% 5.84/2.15  #Fact    : 1
% 5.84/2.15  #Define  : 0
% 5.84/2.15  #Split   : 2
% 5.84/2.15  #Chain   : 0
% 5.84/2.15  #Close   : 0
% 5.84/2.15  
% 5.84/2.15  Ordering : KBO
% 5.84/2.15  
% 5.84/2.15  Simplification rules
% 5.84/2.15  ----------------------
% 5.84/2.15  #Subsume      : 275
% 5.84/2.15  #Demod        : 458
% 5.84/2.15  #Tautology    : 508
% 5.84/2.15  #SimpNegUnit  : 108
% 5.84/2.15  #BackRed      : 4
% 5.84/2.15  
% 5.84/2.15  #Partial instantiations: 0
% 5.84/2.15  #Strategies tried      : 1
% 5.84/2.15  
% 5.84/2.15  Timing (in seconds)
% 5.84/2.15  ----------------------
% 5.84/2.15  Preprocessing        : 0.36
% 5.84/2.15  Parsing              : 0.18
% 5.84/2.15  CNF conversion       : 0.03
% 5.84/2.15  Main loop            : 1.03
% 5.84/2.15  Inferencing          : 0.34
% 5.84/2.15  Reduction            : 0.31
% 5.84/2.15  Demodulation         : 0.23
% 5.84/2.15  BG Simplification    : 0.05
% 5.84/2.15  Subsumption          : 0.24
% 5.84/2.15  Abstraction          : 0.06
% 5.84/2.15  MUC search           : 0.00
% 5.84/2.15  Cooper               : 0.00
% 5.84/2.15  Total                : 1.43
% 5.84/2.15  Index Insertion      : 0.00
% 5.84/2.15  Index Deletion       : 0.00
% 5.84/2.16  Index Matching       : 0.00
% 5.84/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
