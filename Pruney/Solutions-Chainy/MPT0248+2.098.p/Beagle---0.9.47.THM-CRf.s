%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:17 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 228 expanded)
%              Number of leaves         :   35 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  134 ( 523 expanded)
%              Number of equality atoms :   63 ( 389 expanded)
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

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_82,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_117,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_80,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_119,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_86,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_40,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_40])).

tff(c_1248,plain,(
    ! [B_174,A_175] :
      ( k1_tarski(B_174) = A_175
      | k1_xboole_0 = A_175
      | ~ r1_tarski(A_175,k1_tarski(B_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1251,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_123,c_1248])).

tff(c_1262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_119,c_1251])).

tff(c_1264,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_84,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1312,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_1264,c_84])).

tff(c_1263,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1274,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_86])).

tff(c_1720,plain,(
    ! [D_222,B_223,A_224] :
      ( ~ r2_hidden(D_222,B_223)
      | r2_hidden(D_222,k2_xboole_0(A_224,B_223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1733,plain,(
    ! [D_225] :
      ( ~ r2_hidden(D_225,'#skF_8')
      | r2_hidden(D_225,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1274,c_1720])).

tff(c_1283,plain,(
    ! [C_176,A_177] :
      ( C_176 = A_177
      | ~ r2_hidden(C_176,k1_tarski(A_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1286,plain,(
    ! [C_176] :
      ( C_176 = '#skF_6'
      | ~ r2_hidden(C_176,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_1283])).

tff(c_1762,plain,(
    ! [D_231] :
      ( D_231 = '#skF_6'
      | ~ r2_hidden(D_231,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1733,c_1286])).

tff(c_1766,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_1762])).

tff(c_1769,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1263,c_1766])).

tff(c_1773,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1769,c_20])).

tff(c_1776,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1263,c_1773])).

tff(c_54,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3249,plain,(
    ! [A_345,B_346,C_347] :
      ( r1_tarski(k2_tarski(A_345,B_346),C_347)
      | ~ r2_hidden(B_346,C_347)
      | ~ r2_hidden(A_345,C_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3282,plain,(
    ! [A_348,C_349] :
      ( r1_tarski(k1_tarski(A_348),C_349)
      | ~ r2_hidden(A_348,C_349)
      | ~ r2_hidden(A_348,C_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_3249])).

tff(c_3362,plain,(
    ! [C_352] :
      ( r1_tarski('#skF_7',C_352)
      | ~ r2_hidden('#skF_6',C_352)
      | ~ r2_hidden('#skF_6',C_352) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_3282])).

tff(c_3396,plain,
    ( r1_tarski('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_1776,c_3362])).

tff(c_3450,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1776,c_3396])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3477,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3450,c_32])).

tff(c_3570,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3477,c_1274])).

tff(c_3572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1312,c_3570])).

tff(c_3573,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3623,plain,(
    ! [A_364,B_365] :
      ( k2_xboole_0(A_364,B_365) = B_365
      | ~ r1_tarski(A_364,B_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3635,plain,(
    ! [B_10] : k2_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_26,c_3623])).

tff(c_3574,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_3616,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | A_7 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3574,c_20])).

tff(c_3708,plain,(
    ! [D_375,B_376,A_377] :
      ( ~ r2_hidden(D_375,B_376)
      | r2_hidden(D_375,k2_xboole_0(A_377,B_376)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3718,plain,(
    ! [D_378] :
      ( ~ r2_hidden(D_378,'#skF_8')
      | r2_hidden(D_378,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_3708])).

tff(c_42,plain,(
    ! [C_28,A_24] :
      ( C_28 = A_24
      | ~ r2_hidden(C_28,k1_tarski(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3723,plain,(
    ! [D_379] :
      ( D_379 = '#skF_6'
      | ~ r2_hidden(D_379,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3718,c_42])).

tff(c_3728,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3616,c_3723])).

tff(c_3729,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3728])).

tff(c_3737,plain,(
    k2_xboole_0('#skF_8','#skF_8') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3729,c_86])).

tff(c_3739,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_3737])).

tff(c_3741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3573,c_3739])).

tff(c_3743,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3728])).

tff(c_3742,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3728])).

tff(c_3747,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_3742,c_3616])).

tff(c_3750,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_3743,c_3747])).

tff(c_4680,plain,(
    ! [A_479,B_480,C_481] :
      ( r1_tarski(k2_tarski(A_479,B_480),C_481)
      | ~ r2_hidden(B_480,C_481)
      | ~ r2_hidden(A_479,C_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4705,plain,(
    ! [A_482,C_483] :
      ( r1_tarski(k1_tarski(A_482),C_483)
      | ~ r2_hidden(A_482,C_483)
      | ~ r2_hidden(A_482,C_483) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_4680])).

tff(c_66,plain,(
    ! [B_40] : r1_tarski(k1_xboole_0,k1_tarski(B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3577,plain,(
    ! [B_40] : r1_tarski('#skF_7',k1_tarski(B_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3574,c_66])).

tff(c_3634,plain,(
    ! [B_40] : k2_xboole_0('#skF_7',k1_tarski(B_40)) = k1_tarski(B_40) ),
    inference(resolution,[status(thm)],[c_3577,c_3623])).

tff(c_3779,plain,(
    ! [A_383,C_384,B_385] :
      ( r1_tarski(A_383,C_384)
      | ~ r1_tarski(k2_xboole_0(A_383,B_385),C_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3782,plain,(
    ! [C_384,B_40] :
      ( r1_tarski('#skF_7',C_384)
      | ~ r1_tarski(k1_tarski(B_40),C_384) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3634,c_3779])).

tff(c_4778,plain,(
    ! [C_488,A_489] :
      ( r1_tarski('#skF_7',C_488)
      | ~ r2_hidden(A_489,C_488) ) ),
    inference(resolution,[status(thm)],[c_4705,c_3782])).

tff(c_4832,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_3750,c_4778])).

tff(c_4847,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4832,c_32])).

tff(c_4848,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4847,c_86])).

tff(c_4850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3573,c_4848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.90  
% 4.76/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.90  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 4.76/1.90  
% 4.76/1.90  %Foreground sorts:
% 4.76/1.90  
% 4.76/1.90  
% 4.76/1.90  %Background operators:
% 4.76/1.90  
% 4.76/1.90  
% 4.76/1.90  %Foreground operators:
% 4.76/1.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.76/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.76/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.76/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.76/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.76/1.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.76/1.90  tff('#skF_7', type, '#skF_7': $i).
% 4.76/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.76/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.76/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.76/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.76/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.76/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.76/1.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.76/1.90  tff('#skF_8', type, '#skF_8': $i).
% 4.76/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.76/1.90  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.76/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.76/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.76/1.90  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.76/1.90  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.76/1.90  
% 4.76/1.92  tff(f_119, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.76/1.92  tff(f_66, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.76/1.92  tff(f_87, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.76/1.92  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.76/1.92  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.76/1.92  tff(f_73, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.76/1.92  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.76/1.92  tff(f_100, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.76/1.92  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.76/1.92  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.76/1.92  tff(f_54, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.76/1.92  tff(c_82, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.76/1.92  tff(c_117, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_82])).
% 4.76/1.92  tff(c_80, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.76/1.92  tff(c_119, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_80])).
% 4.76/1.92  tff(c_86, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.76/1.92  tff(c_40, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.76/1.92  tff(c_123, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_40])).
% 4.76/1.92  tff(c_1248, plain, (![B_174, A_175]: (k1_tarski(B_174)=A_175 | k1_xboole_0=A_175 | ~r1_tarski(A_175, k1_tarski(B_174)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.76/1.92  tff(c_1251, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_123, c_1248])).
% 4.76/1.92  tff(c_1262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_119, c_1251])).
% 4.76/1.92  tff(c_1264, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 4.76/1.92  tff(c_84, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.76/1.92  tff(c_1312, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1264, c_1264, c_84])).
% 4.76/1.92  tff(c_1263, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 4.76/1.92  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.76/1.92  tff(c_1274, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1264, c_86])).
% 4.76/1.92  tff(c_1720, plain, (![D_222, B_223, A_224]: (~r2_hidden(D_222, B_223) | r2_hidden(D_222, k2_xboole_0(A_224, B_223)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.76/1.92  tff(c_1733, plain, (![D_225]: (~r2_hidden(D_225, '#skF_8') | r2_hidden(D_225, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1274, c_1720])).
% 4.76/1.92  tff(c_1283, plain, (![C_176, A_177]: (C_176=A_177 | ~r2_hidden(C_176, k1_tarski(A_177)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.76/1.92  tff(c_1286, plain, (![C_176]: (C_176='#skF_6' | ~r2_hidden(C_176, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1264, c_1283])).
% 4.76/1.92  tff(c_1762, plain, (![D_231]: (D_231='#skF_6' | ~r2_hidden(D_231, '#skF_8'))), inference(resolution, [status(thm)], [c_1733, c_1286])).
% 4.76/1.92  tff(c_1766, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_1762])).
% 4.76/1.92  tff(c_1769, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1263, c_1766])).
% 4.76/1.92  tff(c_1773, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1769, c_20])).
% 4.76/1.92  tff(c_1776, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1263, c_1773])).
% 4.76/1.92  tff(c_54, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.76/1.92  tff(c_3249, plain, (![A_345, B_346, C_347]: (r1_tarski(k2_tarski(A_345, B_346), C_347) | ~r2_hidden(B_346, C_347) | ~r2_hidden(A_345, C_347))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.76/1.92  tff(c_3282, plain, (![A_348, C_349]: (r1_tarski(k1_tarski(A_348), C_349) | ~r2_hidden(A_348, C_349) | ~r2_hidden(A_348, C_349))), inference(superposition, [status(thm), theory('equality')], [c_54, c_3249])).
% 4.76/1.92  tff(c_3362, plain, (![C_352]: (r1_tarski('#skF_7', C_352) | ~r2_hidden('#skF_6', C_352) | ~r2_hidden('#skF_6', C_352))), inference(superposition, [status(thm), theory('equality')], [c_1264, c_3282])).
% 4.76/1.92  tff(c_3396, plain, (r1_tarski('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_1776, c_3362])).
% 4.76/1.92  tff(c_3450, plain, (r1_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1776, c_3396])).
% 4.76/1.92  tff(c_32, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.76/1.92  tff(c_3477, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_3450, c_32])).
% 4.76/1.92  tff(c_3570, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3477, c_1274])).
% 4.76/1.92  tff(c_3572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1312, c_3570])).
% 4.76/1.92  tff(c_3573, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_82])).
% 4.76/1.92  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.76/1.92  tff(c_3623, plain, (![A_364, B_365]: (k2_xboole_0(A_364, B_365)=B_365 | ~r1_tarski(A_364, B_365))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.76/1.92  tff(c_3635, plain, (![B_10]: (k2_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_26, c_3623])).
% 4.76/1.92  tff(c_3574, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_82])).
% 4.76/1.92  tff(c_3616, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | A_7='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3574, c_20])).
% 4.76/1.92  tff(c_3708, plain, (![D_375, B_376, A_377]: (~r2_hidden(D_375, B_376) | r2_hidden(D_375, k2_xboole_0(A_377, B_376)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.76/1.92  tff(c_3718, plain, (![D_378]: (~r2_hidden(D_378, '#skF_8') | r2_hidden(D_378, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_86, c_3708])).
% 4.76/1.92  tff(c_42, plain, (![C_28, A_24]: (C_28=A_24 | ~r2_hidden(C_28, k1_tarski(A_24)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.76/1.92  tff(c_3723, plain, (![D_379]: (D_379='#skF_6' | ~r2_hidden(D_379, '#skF_8'))), inference(resolution, [status(thm)], [c_3718, c_42])).
% 4.76/1.92  tff(c_3728, plain, ('#skF_3'('#skF_8')='#skF_6' | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_3616, c_3723])).
% 4.76/1.92  tff(c_3729, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_3728])).
% 4.76/1.92  tff(c_3737, plain, (k2_xboole_0('#skF_8', '#skF_8')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3729, c_86])).
% 4.76/1.92  tff(c_3739, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_3737])).
% 4.76/1.92  tff(c_3741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3573, c_3739])).
% 4.76/1.92  tff(c_3743, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_3728])).
% 4.76/1.92  tff(c_3742, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_3728])).
% 4.76/1.92  tff(c_3747, plain, (r2_hidden('#skF_6', '#skF_8') | '#skF_7'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_3742, c_3616])).
% 4.76/1.92  tff(c_3750, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_3743, c_3747])).
% 4.76/1.92  tff(c_4680, plain, (![A_479, B_480, C_481]: (r1_tarski(k2_tarski(A_479, B_480), C_481) | ~r2_hidden(B_480, C_481) | ~r2_hidden(A_479, C_481))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.76/1.92  tff(c_4705, plain, (![A_482, C_483]: (r1_tarski(k1_tarski(A_482), C_483) | ~r2_hidden(A_482, C_483) | ~r2_hidden(A_482, C_483))), inference(superposition, [status(thm), theory('equality')], [c_54, c_4680])).
% 4.76/1.92  tff(c_66, plain, (![B_40]: (r1_tarski(k1_xboole_0, k1_tarski(B_40)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.76/1.92  tff(c_3577, plain, (![B_40]: (r1_tarski('#skF_7', k1_tarski(B_40)))), inference(demodulation, [status(thm), theory('equality')], [c_3574, c_66])).
% 4.76/1.92  tff(c_3634, plain, (![B_40]: (k2_xboole_0('#skF_7', k1_tarski(B_40))=k1_tarski(B_40))), inference(resolution, [status(thm)], [c_3577, c_3623])).
% 4.76/1.92  tff(c_3779, plain, (![A_383, C_384, B_385]: (r1_tarski(A_383, C_384) | ~r1_tarski(k2_xboole_0(A_383, B_385), C_384))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.76/1.92  tff(c_3782, plain, (![C_384, B_40]: (r1_tarski('#skF_7', C_384) | ~r1_tarski(k1_tarski(B_40), C_384))), inference(superposition, [status(thm), theory('equality')], [c_3634, c_3779])).
% 4.76/1.92  tff(c_4778, plain, (![C_488, A_489]: (r1_tarski('#skF_7', C_488) | ~r2_hidden(A_489, C_488))), inference(resolution, [status(thm)], [c_4705, c_3782])).
% 4.76/1.92  tff(c_4832, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_3750, c_4778])).
% 4.76/1.92  tff(c_4847, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_4832, c_32])).
% 4.76/1.92  tff(c_4848, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4847, c_86])).
% 4.76/1.92  tff(c_4850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3573, c_4848])).
% 4.76/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.92  
% 4.76/1.92  Inference rules
% 4.76/1.92  ----------------------
% 4.76/1.92  #Ref     : 0
% 4.76/1.92  #Sup     : 1037
% 4.76/1.92  #Fact    : 0
% 4.76/1.92  #Define  : 0
% 4.76/1.92  #Split   : 5
% 4.76/1.92  #Chain   : 0
% 4.76/1.92  #Close   : 0
% 4.76/1.92  
% 4.76/1.92  Ordering : KBO
% 4.76/1.92  
% 4.76/1.92  Simplification rules
% 4.76/1.92  ----------------------
% 4.76/1.92  #Subsume      : 101
% 4.76/1.92  #Demod        : 565
% 4.76/1.92  #Tautology    : 655
% 4.76/1.92  #SimpNegUnit  : 80
% 4.76/1.92  #BackRed      : 36
% 4.76/1.92  
% 4.76/1.92  #Partial instantiations: 0
% 4.76/1.92  #Strategies tried      : 1
% 4.76/1.92  
% 4.76/1.92  Timing (in seconds)
% 4.76/1.92  ----------------------
% 4.76/1.92  Preprocessing        : 0.33
% 4.76/1.92  Parsing              : 0.16
% 4.76/1.92  CNF conversion       : 0.03
% 4.76/1.92  Main loop            : 0.83
% 4.76/1.92  Inferencing          : 0.31
% 4.76/1.92  Reduction            : 0.29
% 4.76/1.92  Demodulation         : 0.21
% 4.76/1.92  BG Simplification    : 0.03
% 4.76/1.92  Subsumption          : 0.13
% 4.76/1.92  Abstraction          : 0.04
% 4.76/1.92  MUC search           : 0.00
% 4.76/1.92  Cooper               : 0.00
% 4.76/1.92  Total                : 1.19
% 4.76/1.92  Index Insertion      : 0.00
% 4.76/1.92  Index Deletion       : 0.00
% 4.76/1.92  Index Matching       : 0.00
% 4.76/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
