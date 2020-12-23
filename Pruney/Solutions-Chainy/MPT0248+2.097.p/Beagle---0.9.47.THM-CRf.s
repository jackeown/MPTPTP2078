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
% DateTime   : Thu Dec  3 09:50:17 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.58s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 225 expanded)
%              Number of leaves         :   35 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  131 ( 516 expanded)
%              Number of equality atoms :   63 ( 387 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_73,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_80,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_112,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_78,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_121,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_84,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_113,plain,(
    ! [A_53,B_54] : r1_tarski(A_53,k2_xboole_0(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_116,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_113])).

tff(c_953,plain,(
    ! [B_156,A_157] :
      ( k1_tarski(B_156) = A_157
      | k1_xboole_0 = A_157
      | ~ r1_tarski(A_157,k1_tarski(B_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_956,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_116,c_953])).

tff(c_967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_121,c_956])).

tff(c_969,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_82,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_981,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_969,c_82])).

tff(c_968,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_970,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_84])).

tff(c_1474,plain,(
    ! [D_217,B_218,A_219] :
      ( ~ r2_hidden(D_217,B_218)
      | r2_hidden(D_217,k2_xboole_0(A_219,B_218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1511,plain,(
    ! [D_225] :
      ( ~ r2_hidden(D_225,'#skF_8')
      | r2_hidden(D_225,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_1474])).

tff(c_1005,plain,(
    ! [C_161,A_162] :
      ( C_161 = A_162
      | ~ r2_hidden(C_161,k1_tarski(A_162)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1012,plain,(
    ! [C_161] :
      ( C_161 = '#skF_6'
      | ~ r2_hidden(C_161,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_969,c_1005])).

tff(c_1516,plain,(
    ! [D_226] :
      ( D_226 = '#skF_6'
      | ~ r2_hidden(D_226,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1511,c_1012])).

tff(c_1524,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_22,c_1516])).

tff(c_1529,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_968,c_1524])).

tff(c_1533,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1529,c_22])).

tff(c_1536,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_968,c_1533])).

tff(c_52,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2786,plain,(
    ! [A_319,B_320,C_321] :
      ( r1_tarski(k2_tarski(A_319,B_320),C_321)
      | ~ r2_hidden(B_320,C_321)
      | ~ r2_hidden(A_319,C_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2819,plain,(
    ! [A_322,C_323] :
      ( r1_tarski(k1_tarski(A_322),C_323)
      | ~ r2_hidden(A_322,C_323)
      | ~ r2_hidden(A_322,C_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2786])).

tff(c_2990,plain,(
    ! [C_330] :
      ( r1_tarski('#skF_7',C_330)
      | ~ r2_hidden('#skF_6',C_330)
      | ~ r2_hidden('#skF_6',C_330) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_969,c_2819])).

tff(c_3011,plain,
    ( r1_tarski('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_1536,c_2990])).

tff(c_3065,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_3011])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3114,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3065,c_34])).

tff(c_3115,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3114,c_970])).

tff(c_3117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_981,c_3115])).

tff(c_3118,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3119,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_3137,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | A_9 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3119,c_22])).

tff(c_3295,plain,(
    ! [D_361,B_362,A_363] :
      ( ~ r2_hidden(D_361,B_362)
      | r2_hidden(D_361,k2_xboole_0(A_363,B_362)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3318,plain,(
    ! [D_366] :
      ( ~ r2_hidden(D_366,'#skF_8')
      | r2_hidden(D_366,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_3295])).

tff(c_40,plain,(
    ! [C_28,A_24] :
      ( C_28 = A_24
      | ~ r2_hidden(C_28,k1_tarski(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3323,plain,(
    ! [D_367] :
      ( D_367 = '#skF_6'
      | ~ r2_hidden(D_367,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3318,c_40])).

tff(c_3328,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3137,c_3323])).

tff(c_3329,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3328])).

tff(c_3338,plain,(
    k2_xboole_0('#skF_8','#skF_8') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3329,c_84])).

tff(c_3339,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3338])).

tff(c_3341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3118,c_3339])).

tff(c_3343,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3328])).

tff(c_3342,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3328])).

tff(c_3362,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_3342,c_3137])).

tff(c_3365,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_3343,c_3362])).

tff(c_4213,plain,(
    ! [A_463,B_464,C_465] :
      ( r1_tarski(k2_tarski(A_463,B_464),C_465)
      | ~ r2_hidden(B_464,C_465)
      | ~ r2_hidden(A_463,C_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4308,plain,(
    ! [A_469,C_470] :
      ( r1_tarski(k1_tarski(A_469),C_470)
      | ~ r2_hidden(A_469,C_470)
      | ~ r2_hidden(A_469,C_470) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4213])).

tff(c_64,plain,(
    ! [B_40] : r1_tarski(k1_xboole_0,k1_tarski(B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3120,plain,(
    ! [B_40] : r1_tarski('#skF_7',k1_tarski(B_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3119,c_64])).

tff(c_3184,plain,(
    ! [A_342,B_343] :
      ( k2_xboole_0(A_342,B_343) = B_343
      | ~ r1_tarski(A_342,B_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3195,plain,(
    ! [B_40] : k2_xboole_0('#skF_7',k1_tarski(B_40)) = k1_tarski(B_40) ),
    inference(resolution,[status(thm)],[c_3120,c_3184])).

tff(c_3402,plain,(
    ! [A_379,C_380,B_381] :
      ( r1_tarski(A_379,C_380)
      | ~ r1_tarski(k2_xboole_0(A_379,B_381),C_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3405,plain,(
    ! [C_380,B_40] :
      ( r1_tarski('#skF_7',C_380)
      | ~ r1_tarski(k1_tarski(B_40),C_380) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3195,c_3402])).

tff(c_4343,plain,(
    ! [C_472,A_473] :
      ( r1_tarski('#skF_7',C_472)
      | ~ r2_hidden(A_473,C_472) ) ),
    inference(resolution,[status(thm)],[c_4308,c_3405])).

tff(c_4398,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_3365,c_4343])).

tff(c_4436,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4398,c_34])).

tff(c_4437,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4436,c_84])).

tff(c_4439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3118,c_4437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.84  
% 4.58/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.84  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 4.58/1.84  
% 4.58/1.84  %Foreground sorts:
% 4.58/1.84  
% 4.58/1.84  
% 4.58/1.84  %Background operators:
% 4.58/1.84  
% 4.58/1.84  
% 4.58/1.84  %Foreground operators:
% 4.58/1.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.58/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.58/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.58/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.58/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.58/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.58/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.58/1.84  tff('#skF_7', type, '#skF_7': $i).
% 4.58/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.58/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.58/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.58/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.58/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.58/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.58/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.58/1.84  tff('#skF_8', type, '#skF_8': $i).
% 4.58/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.58/1.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.58/1.84  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.58/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.58/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.58/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.58/1.84  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.58/1.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.58/1.84  
% 4.58/1.86  tff(f_117, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.58/1.86  tff(f_64, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.58/1.86  tff(f_85, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.58/1.86  tff(f_44, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.58/1.86  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.58/1.86  tff(f_71, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.58/1.86  tff(f_73, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.58/1.86  tff(f_98, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.58/1.86  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.58/1.86  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.58/1.86  tff(f_56, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.58/1.86  tff(c_80, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.58/1.86  tff(c_112, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_80])).
% 4.58/1.86  tff(c_78, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.58/1.86  tff(c_121, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_78])).
% 4.58/1.86  tff(c_84, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.58/1.86  tff(c_113, plain, (![A_53, B_54]: (r1_tarski(A_53, k2_xboole_0(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.58/1.86  tff(c_116, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_113])).
% 4.58/1.86  tff(c_953, plain, (![B_156, A_157]: (k1_tarski(B_156)=A_157 | k1_xboole_0=A_157 | ~r1_tarski(A_157, k1_tarski(B_156)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.58/1.86  tff(c_956, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_116, c_953])).
% 4.58/1.86  tff(c_967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_121, c_956])).
% 4.58/1.86  tff(c_969, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_78])).
% 4.58/1.86  tff(c_82, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.58/1.86  tff(c_981, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_969, c_969, c_82])).
% 4.58/1.86  tff(c_968, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_78])).
% 4.58/1.86  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.58/1.86  tff(c_970, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_969, c_84])).
% 4.58/1.86  tff(c_1474, plain, (![D_217, B_218, A_219]: (~r2_hidden(D_217, B_218) | r2_hidden(D_217, k2_xboole_0(A_219, B_218)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.58/1.86  tff(c_1511, plain, (![D_225]: (~r2_hidden(D_225, '#skF_8') | r2_hidden(D_225, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_970, c_1474])).
% 4.58/1.86  tff(c_1005, plain, (![C_161, A_162]: (C_161=A_162 | ~r2_hidden(C_161, k1_tarski(A_162)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.58/1.86  tff(c_1012, plain, (![C_161]: (C_161='#skF_6' | ~r2_hidden(C_161, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_969, c_1005])).
% 4.58/1.86  tff(c_1516, plain, (![D_226]: (D_226='#skF_6' | ~r2_hidden(D_226, '#skF_8'))), inference(resolution, [status(thm)], [c_1511, c_1012])).
% 4.58/1.86  tff(c_1524, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_22, c_1516])).
% 4.58/1.86  tff(c_1529, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_968, c_1524])).
% 4.58/1.86  tff(c_1533, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1529, c_22])).
% 4.58/1.86  tff(c_1536, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_968, c_1533])).
% 4.58/1.86  tff(c_52, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.58/1.86  tff(c_2786, plain, (![A_319, B_320, C_321]: (r1_tarski(k2_tarski(A_319, B_320), C_321) | ~r2_hidden(B_320, C_321) | ~r2_hidden(A_319, C_321))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.58/1.86  tff(c_2819, plain, (![A_322, C_323]: (r1_tarski(k1_tarski(A_322), C_323) | ~r2_hidden(A_322, C_323) | ~r2_hidden(A_322, C_323))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2786])).
% 4.58/1.86  tff(c_2990, plain, (![C_330]: (r1_tarski('#skF_7', C_330) | ~r2_hidden('#skF_6', C_330) | ~r2_hidden('#skF_6', C_330))), inference(superposition, [status(thm), theory('equality')], [c_969, c_2819])).
% 4.58/1.86  tff(c_3011, plain, (r1_tarski('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_1536, c_2990])).
% 4.58/1.86  tff(c_3065, plain, (r1_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_3011])).
% 4.58/1.86  tff(c_34, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.58/1.86  tff(c_3114, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_3065, c_34])).
% 4.58/1.86  tff(c_3115, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3114, c_970])).
% 4.58/1.86  tff(c_3117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_981, c_3115])).
% 4.58/1.86  tff(c_3118, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 4.58/1.86  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.58/1.86  tff(c_3119, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 4.58/1.86  tff(c_3137, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | A_9='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3119, c_22])).
% 4.58/1.86  tff(c_3295, plain, (![D_361, B_362, A_363]: (~r2_hidden(D_361, B_362) | r2_hidden(D_361, k2_xboole_0(A_363, B_362)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.58/1.86  tff(c_3318, plain, (![D_366]: (~r2_hidden(D_366, '#skF_8') | r2_hidden(D_366, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_84, c_3295])).
% 4.58/1.86  tff(c_40, plain, (![C_28, A_24]: (C_28=A_24 | ~r2_hidden(C_28, k1_tarski(A_24)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.58/1.86  tff(c_3323, plain, (![D_367]: (D_367='#skF_6' | ~r2_hidden(D_367, '#skF_8'))), inference(resolution, [status(thm)], [c_3318, c_40])).
% 4.58/1.86  tff(c_3328, plain, ('#skF_3'('#skF_8')='#skF_6' | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_3137, c_3323])).
% 4.58/1.86  tff(c_3329, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_3328])).
% 4.58/1.86  tff(c_3338, plain, (k2_xboole_0('#skF_8', '#skF_8')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3329, c_84])).
% 4.58/1.86  tff(c_3339, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3338])).
% 4.58/1.86  tff(c_3341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3118, c_3339])).
% 4.58/1.86  tff(c_3343, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_3328])).
% 4.58/1.86  tff(c_3342, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_3328])).
% 4.58/1.86  tff(c_3362, plain, (r2_hidden('#skF_6', '#skF_8') | '#skF_7'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_3342, c_3137])).
% 4.58/1.86  tff(c_3365, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_3343, c_3362])).
% 4.58/1.86  tff(c_4213, plain, (![A_463, B_464, C_465]: (r1_tarski(k2_tarski(A_463, B_464), C_465) | ~r2_hidden(B_464, C_465) | ~r2_hidden(A_463, C_465))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.58/1.86  tff(c_4308, plain, (![A_469, C_470]: (r1_tarski(k1_tarski(A_469), C_470) | ~r2_hidden(A_469, C_470) | ~r2_hidden(A_469, C_470))), inference(superposition, [status(thm), theory('equality')], [c_52, c_4213])).
% 4.58/1.86  tff(c_64, plain, (![B_40]: (r1_tarski(k1_xboole_0, k1_tarski(B_40)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.58/1.86  tff(c_3120, plain, (![B_40]: (r1_tarski('#skF_7', k1_tarski(B_40)))), inference(demodulation, [status(thm), theory('equality')], [c_3119, c_64])).
% 4.58/1.86  tff(c_3184, plain, (![A_342, B_343]: (k2_xboole_0(A_342, B_343)=B_343 | ~r1_tarski(A_342, B_343))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.58/1.86  tff(c_3195, plain, (![B_40]: (k2_xboole_0('#skF_7', k1_tarski(B_40))=k1_tarski(B_40))), inference(resolution, [status(thm)], [c_3120, c_3184])).
% 4.58/1.86  tff(c_3402, plain, (![A_379, C_380, B_381]: (r1_tarski(A_379, C_380) | ~r1_tarski(k2_xboole_0(A_379, B_381), C_380))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.58/1.86  tff(c_3405, plain, (![C_380, B_40]: (r1_tarski('#skF_7', C_380) | ~r1_tarski(k1_tarski(B_40), C_380))), inference(superposition, [status(thm), theory('equality')], [c_3195, c_3402])).
% 4.58/1.86  tff(c_4343, plain, (![C_472, A_473]: (r1_tarski('#skF_7', C_472) | ~r2_hidden(A_473, C_472))), inference(resolution, [status(thm)], [c_4308, c_3405])).
% 4.58/1.86  tff(c_4398, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_3365, c_4343])).
% 4.58/1.86  tff(c_4436, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_4398, c_34])).
% 4.58/1.86  tff(c_4437, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4436, c_84])).
% 4.58/1.86  tff(c_4439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3118, c_4437])).
% 4.58/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.86  
% 4.58/1.86  Inference rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Ref     : 0
% 4.58/1.86  #Sup     : 958
% 4.58/1.86  #Fact    : 0
% 4.58/1.86  #Define  : 0
% 4.58/1.86  #Split   : 5
% 4.58/1.86  #Chain   : 0
% 4.58/1.86  #Close   : 0
% 4.58/1.86  
% 4.58/1.86  Ordering : KBO
% 4.58/1.86  
% 4.58/1.86  Simplification rules
% 4.58/1.86  ----------------------
% 4.58/1.86  #Subsume      : 89
% 4.58/1.86  #Demod        : 527
% 4.58/1.86  #Tautology    : 615
% 4.58/1.86  #SimpNegUnit  : 62
% 4.58/1.86  #BackRed      : 25
% 4.58/1.86  
% 4.58/1.86  #Partial instantiations: 0
% 4.58/1.86  #Strategies tried      : 1
% 4.58/1.86  
% 4.58/1.86  Timing (in seconds)
% 4.58/1.86  ----------------------
% 4.58/1.86  Preprocessing        : 0.34
% 4.58/1.86  Parsing              : 0.17
% 4.58/1.86  CNF conversion       : 0.03
% 4.58/1.86  Main loop            : 0.77
% 4.58/1.86  Inferencing          : 0.27
% 4.58/1.86  Reduction            : 0.28
% 4.58/1.86  Demodulation         : 0.21
% 4.58/1.86  BG Simplification    : 0.03
% 4.58/1.86  Subsumption          : 0.12
% 4.58/1.86  Abstraction          : 0.03
% 4.58/1.86  MUC search           : 0.00
% 4.58/1.86  Cooper               : 0.00
% 4.58/1.86  Total                : 1.13
% 4.58/1.86  Index Insertion      : 0.00
% 4.58/1.86  Index Deletion       : 0.00
% 4.58/1.86  Index Matching       : 0.00
% 4.58/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
