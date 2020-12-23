%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:21 EST 2020

% Result     : Theorem 5.49s
% Output     : CNFRefutation 5.70s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 239 expanded)
%              Number of leaves         :   42 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 ( 471 expanded)
%              Number of equality atoms :   78 ( 423 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

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

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_69,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_80,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_122,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_78,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_120,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_84,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_126,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_30])).

tff(c_837,plain,(
    ! [B_146,A_147] :
      ( k1_tarski(B_146) = A_147
      | k1_xboole_0 = A_147
      | ~ r1_tarski(A_147,k1_tarski(B_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_843,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_126,c_837])).

tff(c_852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_120,c_843])).

tff(c_853,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_854,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_28,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_856,plain,(
    ! [A_14] : k5_xboole_0(A_14,'#skF_7') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_28])).

tff(c_68,plain,(
    ! [B_57] : r1_tarski(k1_xboole_0,k1_tarski(B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_858,plain,(
    ! [B_57] : r1_tarski('#skF_7',k1_tarski(B_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_68])).

tff(c_928,plain,(
    ! [A_157,B_158] :
      ( k2_xboole_0(A_157,B_158) = B_158
      | ~ r1_tarski(A_157,B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_939,plain,(
    ! [B_57] : k2_xboole_0('#skF_7',k1_tarski(B_57)) = k1_tarski(B_57) ),
    inference(resolution,[status(thm)],[c_858,c_928])).

tff(c_26,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_855,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_854,c_26])).

tff(c_1023,plain,(
    ! [A_167,B_168] : k5_xboole_0(A_167,k3_xboole_0(A_167,B_168)) = k4_xboole_0(A_167,B_168) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1032,plain,(
    ! [A_13] : k5_xboole_0(A_13,'#skF_7') = k4_xboole_0(A_13,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_855,c_1023])).

tff(c_1035,plain,(
    ! [A_13] : k4_xboole_0(A_13,'#skF_7') = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_1032])).

tff(c_1296,plain,(
    ! [A_193,B_194] : k5_xboole_0(A_193,k4_xboole_0(B_194,A_193)) = k2_xboole_0(A_193,B_194) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1305,plain,(
    ! [A_13] : k5_xboole_0('#skF_7',A_13) = k2_xboole_0('#skF_7',A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_1296])).

tff(c_1627,plain,(
    ! [A_232,B_233,C_234] : k5_xboole_0(k5_xboole_0(A_232,B_233),C_234) = k5_xboole_0(A_232,k5_xboole_0(B_233,C_234)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_857,plain,(
    ! [A_20] : k5_xboole_0(A_20,A_20) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_34])).

tff(c_1696,plain,(
    ! [A_235,B_236] : k5_xboole_0(A_235,k5_xboole_0(B_236,k5_xboole_0(A_235,B_236))) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1627,c_857])).

tff(c_1751,plain,(
    ! [A_14] : k5_xboole_0(A_14,k5_xboole_0('#skF_7',A_14)) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_1696])).

tff(c_1763,plain,(
    ! [A_14] : k5_xboole_0(A_14,k2_xboole_0('#skF_7',A_14)) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1751])).

tff(c_1764,plain,(
    ! [A_237] : k5_xboole_0(A_237,k2_xboole_0('#skF_7',A_237)) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1751])).

tff(c_1807,plain,(
    k5_xboole_0('#skF_8',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_1764])).

tff(c_32,plain,(
    ! [A_17,B_18,C_19] : k5_xboole_0(k5_xboole_0(A_17,B_18),C_19) = k5_xboole_0(A_17,k5_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1824,plain,(
    ! [C_19] : k5_xboole_0('#skF_8',k5_xboole_0(k1_tarski('#skF_6'),C_19)) = k5_xboole_0('#skF_7',C_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_1807,c_32])).

tff(c_1830,plain,(
    ! [C_238] : k5_xboole_0('#skF_8',k5_xboole_0(k1_tarski('#skF_6'),C_238)) = k2_xboole_0('#skF_7',C_238) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1824])).

tff(c_1854,plain,(
    k2_xboole_0('#skF_7',k2_xboole_0('#skF_7',k1_tarski('#skF_6'))) = k5_xboole_0('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1763,c_1830])).

tff(c_1885,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_939,c_939,c_1854])).

tff(c_1887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_853,c_1885])).

tff(c_1889,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_82,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1946,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1889,c_1889,c_82])).

tff(c_1888,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1911,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1889,c_84])).

tff(c_2372,plain,(
    ! [D_283,B_284,A_285] :
      ( ~ r2_hidden(D_283,B_284)
      | r2_hidden(D_283,k2_xboole_0(A_285,B_284)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2403,plain,(
    ! [D_286] :
      ( ~ r2_hidden(D_286,'#skF_8')
      | r2_hidden(D_286,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1911,c_2372])).

tff(c_1930,plain,(
    ! [C_243,A_244] :
      ( C_243 = A_244
      | ~ r2_hidden(C_243,k1_tarski(A_244)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1933,plain,(
    ! [C_243] :
      ( C_243 = '#skF_6'
      | ~ r2_hidden(C_243,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1889,c_1930])).

tff(c_2408,plain,(
    ! [D_287] :
      ( D_287 = '#skF_6'
      | ~ r2_hidden(D_287,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2403,c_1933])).

tff(c_2416,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_2408])).

tff(c_2421,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1888,c_2416])).

tff(c_2453,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2421,c_20])).

tff(c_2456,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1888,c_2453])).

tff(c_50,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3909,plain,(
    ! [A_359,B_360,C_361] :
      ( r1_tarski(k2_tarski(A_359,B_360),C_361)
      | ~ r2_hidden(B_360,C_361)
      | ~ r2_hidden(A_359,C_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7023,plain,(
    ! [A_472,C_473] :
      ( r1_tarski(k1_tarski(A_472),C_473)
      | ~ r2_hidden(A_472,C_473)
      | ~ r2_hidden(A_472,C_473) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_3909])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7043,plain,(
    ! [A_474,C_475] :
      ( k2_xboole_0(k1_tarski(A_474),C_475) = C_475
      | ~ r2_hidden(A_474,C_475) ) ),
    inference(resolution,[status(thm)],[c_7023,c_24])).

tff(c_7285,plain,(
    ! [C_479] :
      ( k2_xboole_0('#skF_7',C_479) = C_479
      | ~ r2_hidden('#skF_6',C_479) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1889,c_7043])).

tff(c_7351,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2456,c_7285])).

tff(c_7372,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7351,c_1911])).

tff(c_7374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1946,c_7372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.49/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.24  
% 5.70/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.24  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 5.70/2.24  
% 5.70/2.24  %Foreground sorts:
% 5.70/2.24  
% 5.70/2.24  
% 5.70/2.24  %Background operators:
% 5.70/2.24  
% 5.70/2.24  
% 5.70/2.24  %Foreground operators:
% 5.70/2.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.70/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.70/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.70/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.70/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.70/2.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.70/2.24  tff('#skF_7', type, '#skF_7': $i).
% 5.70/2.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.70/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.70/2.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.70/2.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.70/2.24  tff('#skF_6', type, '#skF_6': $i).
% 5.70/2.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.70/2.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.70/2.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.70/2.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.70/2.24  tff('#skF_8', type, '#skF_8': $i).
% 5.70/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.70/2.24  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.70/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.70/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.70/2.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.70/2.24  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.70/2.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.70/2.24  
% 5.70/2.26  tff(f_114, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 5.70/2.26  tff(f_54, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.70/2.26  tff(f_87, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.70/2.26  tff(f_52, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.70/2.26  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.70/2.26  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.70/2.26  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.70/2.26  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.70/2.26  tff(f_56, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.70/2.26  tff(f_58, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.70/2.26  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.70/2.26  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 5.70/2.26  tff(f_67, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 5.70/2.26  tff(f_69, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.70/2.26  tff(f_95, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 5.70/2.26  tff(c_80, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.70/2.26  tff(c_122, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_80])).
% 5.70/2.26  tff(c_78, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.70/2.26  tff(c_120, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_78])).
% 5.70/2.26  tff(c_84, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.70/2.26  tff(c_30, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.70/2.26  tff(c_126, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_30])).
% 5.70/2.26  tff(c_837, plain, (![B_146, A_147]: (k1_tarski(B_146)=A_147 | k1_xboole_0=A_147 | ~r1_tarski(A_147, k1_tarski(B_146)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.70/2.26  tff(c_843, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_126, c_837])).
% 5.70/2.26  tff(c_852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_120, c_843])).
% 5.70/2.26  tff(c_853, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 5.70/2.26  tff(c_854, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 5.70/2.26  tff(c_28, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.70/2.26  tff(c_856, plain, (![A_14]: (k5_xboole_0(A_14, '#skF_7')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_854, c_28])).
% 5.70/2.26  tff(c_68, plain, (![B_57]: (r1_tarski(k1_xboole_0, k1_tarski(B_57)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.70/2.26  tff(c_858, plain, (![B_57]: (r1_tarski('#skF_7', k1_tarski(B_57)))), inference(demodulation, [status(thm), theory('equality')], [c_854, c_68])).
% 5.70/2.26  tff(c_928, plain, (![A_157, B_158]: (k2_xboole_0(A_157, B_158)=B_158 | ~r1_tarski(A_157, B_158))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.70/2.26  tff(c_939, plain, (![B_57]: (k2_xboole_0('#skF_7', k1_tarski(B_57))=k1_tarski(B_57))), inference(resolution, [status(thm)], [c_858, c_928])).
% 5.70/2.26  tff(c_26, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.70/2.26  tff(c_855, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_854, c_854, c_26])).
% 5.70/2.26  tff(c_1023, plain, (![A_167, B_168]: (k5_xboole_0(A_167, k3_xboole_0(A_167, B_168))=k4_xboole_0(A_167, B_168))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.70/2.26  tff(c_1032, plain, (![A_13]: (k5_xboole_0(A_13, '#skF_7')=k4_xboole_0(A_13, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_855, c_1023])).
% 5.70/2.26  tff(c_1035, plain, (![A_13]: (k4_xboole_0(A_13, '#skF_7')=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_856, c_1032])).
% 5.70/2.26  tff(c_1296, plain, (![A_193, B_194]: (k5_xboole_0(A_193, k4_xboole_0(B_194, A_193))=k2_xboole_0(A_193, B_194))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.70/2.26  tff(c_1305, plain, (![A_13]: (k5_xboole_0('#skF_7', A_13)=k2_xboole_0('#skF_7', A_13))), inference(superposition, [status(thm), theory('equality')], [c_1035, c_1296])).
% 5.70/2.26  tff(c_1627, plain, (![A_232, B_233, C_234]: (k5_xboole_0(k5_xboole_0(A_232, B_233), C_234)=k5_xboole_0(A_232, k5_xboole_0(B_233, C_234)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.70/2.26  tff(c_34, plain, (![A_20]: (k5_xboole_0(A_20, A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.70/2.26  tff(c_857, plain, (![A_20]: (k5_xboole_0(A_20, A_20)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_854, c_34])).
% 5.70/2.26  tff(c_1696, plain, (![A_235, B_236]: (k5_xboole_0(A_235, k5_xboole_0(B_236, k5_xboole_0(A_235, B_236)))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1627, c_857])).
% 5.70/2.26  tff(c_1751, plain, (![A_14]: (k5_xboole_0(A_14, k5_xboole_0('#skF_7', A_14))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_856, c_1696])).
% 5.70/2.26  tff(c_1763, plain, (![A_14]: (k5_xboole_0(A_14, k2_xboole_0('#skF_7', A_14))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1751])).
% 5.70/2.26  tff(c_1764, plain, (![A_237]: (k5_xboole_0(A_237, k2_xboole_0('#skF_7', A_237))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1751])).
% 5.70/2.26  tff(c_1807, plain, (k5_xboole_0('#skF_8', k1_tarski('#skF_6'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_84, c_1764])).
% 5.70/2.26  tff(c_32, plain, (![A_17, B_18, C_19]: (k5_xboole_0(k5_xboole_0(A_17, B_18), C_19)=k5_xboole_0(A_17, k5_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.70/2.26  tff(c_1824, plain, (![C_19]: (k5_xboole_0('#skF_8', k5_xboole_0(k1_tarski('#skF_6'), C_19))=k5_xboole_0('#skF_7', C_19))), inference(superposition, [status(thm), theory('equality')], [c_1807, c_32])).
% 5.70/2.26  tff(c_1830, plain, (![C_238]: (k5_xboole_0('#skF_8', k5_xboole_0(k1_tarski('#skF_6'), C_238))=k2_xboole_0('#skF_7', C_238))), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1824])).
% 5.70/2.26  tff(c_1854, plain, (k2_xboole_0('#skF_7', k2_xboole_0('#skF_7', k1_tarski('#skF_6')))=k5_xboole_0('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1763, c_1830])).
% 5.70/2.26  tff(c_1885, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_856, c_939, c_939, c_1854])).
% 5.70/2.26  tff(c_1887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_853, c_1885])).
% 5.70/2.26  tff(c_1889, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_78])).
% 5.70/2.26  tff(c_82, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.70/2.26  tff(c_1946, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1889, c_1889, c_82])).
% 5.70/2.26  tff(c_1888, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_78])).
% 5.70/2.26  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.70/2.26  tff(c_1911, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1889, c_84])).
% 5.70/2.26  tff(c_2372, plain, (![D_283, B_284, A_285]: (~r2_hidden(D_283, B_284) | r2_hidden(D_283, k2_xboole_0(A_285, B_284)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.70/2.26  tff(c_2403, plain, (![D_286]: (~r2_hidden(D_286, '#skF_8') | r2_hidden(D_286, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1911, c_2372])).
% 5.70/2.26  tff(c_1930, plain, (![C_243, A_244]: (C_243=A_244 | ~r2_hidden(C_243, k1_tarski(A_244)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.70/2.26  tff(c_1933, plain, (![C_243]: (C_243='#skF_6' | ~r2_hidden(C_243, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1889, c_1930])).
% 5.70/2.26  tff(c_2408, plain, (![D_287]: (D_287='#skF_6' | ~r2_hidden(D_287, '#skF_8'))), inference(resolution, [status(thm)], [c_2403, c_1933])).
% 5.70/2.26  tff(c_2416, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_2408])).
% 5.70/2.26  tff(c_2421, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1888, c_2416])).
% 5.70/2.26  tff(c_2453, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_2421, c_20])).
% 5.70/2.26  tff(c_2456, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1888, c_2453])).
% 5.70/2.26  tff(c_50, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.70/2.26  tff(c_3909, plain, (![A_359, B_360, C_361]: (r1_tarski(k2_tarski(A_359, B_360), C_361) | ~r2_hidden(B_360, C_361) | ~r2_hidden(A_359, C_361))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.70/2.26  tff(c_7023, plain, (![A_472, C_473]: (r1_tarski(k1_tarski(A_472), C_473) | ~r2_hidden(A_472, C_473) | ~r2_hidden(A_472, C_473))), inference(superposition, [status(thm), theory('equality')], [c_50, c_3909])).
% 5.70/2.26  tff(c_24, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.70/2.26  tff(c_7043, plain, (![A_474, C_475]: (k2_xboole_0(k1_tarski(A_474), C_475)=C_475 | ~r2_hidden(A_474, C_475))), inference(resolution, [status(thm)], [c_7023, c_24])).
% 5.70/2.26  tff(c_7285, plain, (![C_479]: (k2_xboole_0('#skF_7', C_479)=C_479 | ~r2_hidden('#skF_6', C_479))), inference(superposition, [status(thm), theory('equality')], [c_1889, c_7043])).
% 5.70/2.26  tff(c_7351, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_2456, c_7285])).
% 5.70/2.26  tff(c_7372, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7351, c_1911])).
% 5.70/2.26  tff(c_7374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1946, c_7372])).
% 5.70/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.26  
% 5.70/2.26  Inference rules
% 5.70/2.26  ----------------------
% 5.70/2.26  #Ref     : 0
% 5.70/2.26  #Sup     : 1694
% 5.70/2.26  #Fact    : 10
% 5.70/2.26  #Define  : 0
% 5.70/2.26  #Split   : 10
% 5.70/2.26  #Chain   : 0
% 5.70/2.26  #Close   : 0
% 5.70/2.26  
% 5.70/2.26  Ordering : KBO
% 5.70/2.26  
% 5.70/2.26  Simplification rules
% 5.70/2.26  ----------------------
% 5.70/2.26  #Subsume      : 81
% 5.70/2.26  #Demod        : 1269
% 5.70/2.26  #Tautology    : 1107
% 5.70/2.26  #SimpNegUnit  : 25
% 5.70/2.26  #BackRed      : 63
% 5.70/2.26  
% 5.70/2.26  #Partial instantiations: 0
% 5.70/2.26  #Strategies tried      : 1
% 5.70/2.26  
% 5.70/2.26  Timing (in seconds)
% 5.70/2.26  ----------------------
% 5.70/2.26  Preprocessing        : 0.34
% 5.70/2.26  Parsing              : 0.18
% 5.70/2.26  CNF conversion       : 0.03
% 5.70/2.26  Main loop            : 1.06
% 5.70/2.26  Inferencing          : 0.36
% 5.70/2.26  Reduction            : 0.41
% 5.70/2.26  Demodulation         : 0.32
% 5.70/2.26  BG Simplification    : 0.04
% 5.70/2.26  Subsumption          : 0.17
% 5.70/2.26  Abstraction          : 0.05
% 5.70/2.26  MUC search           : 0.00
% 5.70/2.26  Cooper               : 0.00
% 5.70/2.26  Total                : 1.44
% 5.70/2.26  Index Insertion      : 0.00
% 5.70/2.26  Index Deletion       : 0.00
% 5.70/2.26  Index Matching       : 0.00
% 5.70/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
