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
% DateTime   : Thu Dec  3 09:49:55 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 172 expanded)
%              Number of leaves         :   26 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 308 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),C)
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_46,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_145,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_85,plain,(
    r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_113,plain,(
    ! [A_53,B_54] : k2_xboole_0(k1_tarski(A_53),k1_tarski(B_54)) = k2_tarski(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_186,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(k1_tarski(A_63),C_64)
      | ~ r1_tarski(k2_tarski(A_63,B_65),C_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_2])).

tff(c_194,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_85,c_186])).

tff(c_38,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,B_24)
      | ~ r1_tarski(k1_tarski(A_23),B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_200,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_194,c_38])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_200])).

tff(c_207,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_209,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_48])).

tff(c_210,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_64,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_70,plain,(
    ! [B_41,A_40] : r2_hidden(B_41,k2_tarski(A_40,B_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10])).

tff(c_100,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_tarski(A_48),B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_126,plain,(
    ! [A_55,B_56] :
      ( k2_xboole_0(k1_tarski(A_55),B_56) = B_56
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_100,c_4])).

tff(c_428,plain,(
    ! [A_87,C_88,B_89] :
      ( r1_tarski(k1_tarski(A_87),C_88)
      | ~ r1_tarski(B_89,C_88)
      | ~ r2_hidden(A_87,B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_2])).

tff(c_457,plain,(
    ! [A_91] :
      ( r1_tarski(k1_tarski(A_91),'#skF_8')
      | ~ r2_hidden(A_91,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_85,c_428])).

tff(c_472,plain,(
    r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_457])).

tff(c_508,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_472,c_38])).

tff(c_516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_508])).

tff(c_518,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_206,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_521,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_206])).

tff(c_40,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tarski(A_23),B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_517,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_32,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),k1_tarski(B_17)) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_554,plain,(
    ! [A_103,C_104,B_105] :
      ( r1_tarski(k2_xboole_0(A_103,C_104),B_105)
      | ~ r1_tarski(C_104,B_105)
      | ~ r1_tarski(A_103,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1823,plain,(
    ! [A_275,B_276,B_277] :
      ( r1_tarski(k2_tarski(A_275,B_276),B_277)
      | ~ r1_tarski(k1_tarski(B_276),B_277)
      | ~ r1_tarski(k1_tarski(A_275),B_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_554])).

tff(c_44,plain,
    ( ~ r1_tarski(k2_tarski('#skF_3','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_605,plain,(
    ~ r1_tarski(k2_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_518,c_44])).

tff(c_1845,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1823,c_605])).

tff(c_1848,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1845])).

tff(c_1851,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1848])).

tff(c_1855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_1851])).

tff(c_1856,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1845])).

tff(c_1860,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1856])).

tff(c_1864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_1860])).

tff(c_1865,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1866,plain,(
    ~ r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_54,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1895,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1866,c_54])).

tff(c_1974,plain,(
    ! [A_308,C_309,B_310] :
      ( r1_tarski(k2_xboole_0(A_308,C_309),B_310)
      | ~ r1_tarski(C_309,B_310)
      | ~ r1_tarski(A_308,B_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2067,plain,(
    ! [A_331,B_332,B_333] :
      ( r1_tarski(k2_tarski(A_331,B_332),B_333)
      | ~ r1_tarski(k1_tarski(B_332),B_333)
      | ~ r1_tarski(k1_tarski(A_331),B_333) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1974])).

tff(c_50,plain,
    ( ~ r1_tarski(k2_tarski('#skF_3','#skF_4'),'#skF_5')
    | r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1952,plain,(
    ~ r1_tarski(k2_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1866,c_50])).

tff(c_2083,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_2067,c_1952])).

tff(c_2087,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2083])).

tff(c_2090,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_2087])).

tff(c_2094,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1895,c_2090])).

tff(c_2095,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2083])).

tff(c_2099,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_2095])).

tff(c_2103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1865,c_2099])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.40/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.85  
% 4.40/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.85  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.40/1.85  
% 4.40/1.85  %Foreground sorts:
% 4.40/1.85  
% 4.40/1.85  
% 4.40/1.85  %Background operators:
% 4.40/1.85  
% 4.40/1.85  
% 4.40/1.85  %Foreground operators:
% 4.40/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.40/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.40/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.40/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.40/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.40/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.40/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.40/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.40/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.40/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.40/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.40/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.40/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.40/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.40/1.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.40/1.85  
% 4.40/1.86  tff(f_73, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.40/1.86  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 4.40/1.86  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.40/1.86  tff(f_64, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.40/1.86  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.40/1.86  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.40/1.86  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.40/1.86  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.40/1.86  tff(c_46, plain, (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.40/1.86  tff(c_145, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_46])).
% 4.40/1.86  tff(c_52, plain, (r2_hidden('#skF_4', '#skF_5') | r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.40/1.86  tff(c_85, plain, (r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_52])).
% 4.40/1.86  tff(c_113, plain, (![A_53, B_54]: (k2_xboole_0(k1_tarski(A_53), k1_tarski(B_54))=k2_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.40/1.86  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.40/1.86  tff(c_186, plain, (![A_63, C_64, B_65]: (r1_tarski(k1_tarski(A_63), C_64) | ~r1_tarski(k2_tarski(A_63, B_65), C_64))), inference(superposition, [status(thm), theory('equality')], [c_113, c_2])).
% 4.40/1.86  tff(c_194, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_8')), inference(resolution, [status(thm)], [c_85, c_186])).
% 4.40/1.86  tff(c_38, plain, (![A_23, B_24]: (r2_hidden(A_23, B_24) | ~r1_tarski(k1_tarski(A_23), B_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.40/1.86  tff(c_200, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_194, c_38])).
% 4.40/1.86  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_200])).
% 4.40/1.86  tff(c_207, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_46])).
% 4.40/1.86  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.40/1.86  tff(c_209, plain, (r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_48])).
% 4.40/1.86  tff(c_210, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_209])).
% 4.40/1.86  tff(c_64, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.40/1.86  tff(c_10, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.40/1.86  tff(c_70, plain, (![B_41, A_40]: (r2_hidden(B_41, k2_tarski(A_40, B_41)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_10])).
% 4.40/1.86  tff(c_100, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), B_49) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.40/1.86  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.40/1.86  tff(c_126, plain, (![A_55, B_56]: (k2_xboole_0(k1_tarski(A_55), B_56)=B_56 | ~r2_hidden(A_55, B_56))), inference(resolution, [status(thm)], [c_100, c_4])).
% 4.40/1.86  tff(c_428, plain, (![A_87, C_88, B_89]: (r1_tarski(k1_tarski(A_87), C_88) | ~r1_tarski(B_89, C_88) | ~r2_hidden(A_87, B_89))), inference(superposition, [status(thm), theory('equality')], [c_126, c_2])).
% 4.40/1.86  tff(c_457, plain, (![A_91]: (r1_tarski(k1_tarski(A_91), '#skF_8') | ~r2_hidden(A_91, k2_tarski('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_85, c_428])).
% 4.40/1.86  tff(c_472, plain, (r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_70, c_457])).
% 4.40/1.86  tff(c_508, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_472, c_38])).
% 4.40/1.86  tff(c_516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_508])).
% 4.40/1.86  tff(c_518, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_209])).
% 4.40/1.86  tff(c_206, plain, (~r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 4.40/1.86  tff(c_521, plain, (r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_518, c_206])).
% 4.40/1.86  tff(c_40, plain, (![A_23, B_24]: (r1_tarski(k1_tarski(A_23), B_24) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.40/1.86  tff(c_517, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_209])).
% 4.40/1.86  tff(c_32, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(B_17))=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.40/1.86  tff(c_554, plain, (![A_103, C_104, B_105]: (r1_tarski(k2_xboole_0(A_103, C_104), B_105) | ~r1_tarski(C_104, B_105) | ~r1_tarski(A_103, B_105))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.40/1.86  tff(c_1823, plain, (![A_275, B_276, B_277]: (r1_tarski(k2_tarski(A_275, B_276), B_277) | ~r1_tarski(k1_tarski(B_276), B_277) | ~r1_tarski(k1_tarski(A_275), B_277))), inference(superposition, [status(thm), theory('equality')], [c_32, c_554])).
% 4.40/1.86  tff(c_44, plain, (~r1_tarski(k2_tarski('#skF_3', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.40/1.86  tff(c_605, plain, (~r1_tarski(k2_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_518, c_44])).
% 4.40/1.86  tff(c_1845, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_5') | ~r1_tarski(k1_tarski('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_1823, c_605])).
% 4.40/1.86  tff(c_1848, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1845])).
% 4.40/1.86  tff(c_1851, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_1848])).
% 4.40/1.86  tff(c_1855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_517, c_1851])).
% 4.40/1.86  tff(c_1856, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_1845])).
% 4.40/1.86  tff(c_1860, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_1856])).
% 4.40/1.86  tff(c_1864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_521, c_1860])).
% 4.40/1.86  tff(c_1865, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 4.40/1.86  tff(c_1866, plain, (~r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_52])).
% 4.40/1.86  tff(c_54, plain, (r2_hidden('#skF_3', '#skF_5') | r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.40/1.86  tff(c_1895, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1866, c_54])).
% 4.40/1.86  tff(c_1974, plain, (![A_308, C_309, B_310]: (r1_tarski(k2_xboole_0(A_308, C_309), B_310) | ~r1_tarski(C_309, B_310) | ~r1_tarski(A_308, B_310))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.40/1.86  tff(c_2067, plain, (![A_331, B_332, B_333]: (r1_tarski(k2_tarski(A_331, B_332), B_333) | ~r1_tarski(k1_tarski(B_332), B_333) | ~r1_tarski(k1_tarski(A_331), B_333))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1974])).
% 4.40/1.86  tff(c_50, plain, (~r1_tarski(k2_tarski('#skF_3', '#skF_4'), '#skF_5') | r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.40/1.86  tff(c_1952, plain, (~r1_tarski(k2_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1866, c_50])).
% 4.40/1.86  tff(c_2083, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_5') | ~r1_tarski(k1_tarski('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_2067, c_1952])).
% 4.40/1.86  tff(c_2087, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_2083])).
% 4.40/1.86  tff(c_2090, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_2087])).
% 4.40/1.86  tff(c_2094, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1895, c_2090])).
% 4.40/1.86  tff(c_2095, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_2083])).
% 4.40/1.86  tff(c_2099, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_2095])).
% 4.40/1.86  tff(c_2103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1865, c_2099])).
% 4.40/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.86  
% 4.40/1.86  Inference rules
% 4.40/1.86  ----------------------
% 4.40/1.86  #Ref     : 0
% 4.40/1.86  #Sup     : 497
% 4.40/1.86  #Fact    : 0
% 4.40/1.86  #Define  : 0
% 4.40/1.86  #Split   : 9
% 4.40/1.86  #Chain   : 0
% 4.40/1.86  #Close   : 0
% 4.40/1.86  
% 4.40/1.86  Ordering : KBO
% 4.40/1.86  
% 4.40/1.86  Simplification rules
% 4.40/1.86  ----------------------
% 4.40/1.86  #Subsume      : 126
% 4.40/1.86  #Demod        : 65
% 4.40/1.86  #Tautology    : 164
% 4.40/1.86  #SimpNegUnit  : 4
% 4.40/1.86  #BackRed      : 0
% 4.40/1.86  
% 4.40/1.86  #Partial instantiations: 0
% 4.40/1.86  #Strategies tried      : 1
% 4.40/1.86  
% 4.40/1.86  Timing (in seconds)
% 4.40/1.86  ----------------------
% 4.40/1.87  Preprocessing        : 0.33
% 4.40/1.87  Parsing              : 0.16
% 4.40/1.87  CNF conversion       : 0.03
% 4.40/1.87  Main loop            : 0.70
% 4.40/1.87  Inferencing          : 0.26
% 4.40/1.87  Reduction            : 0.20
% 4.40/1.87  Demodulation         : 0.14
% 4.40/1.87  BG Simplification    : 0.03
% 4.40/1.87  Subsumption          : 0.16
% 4.40/1.87  Abstraction          : 0.04
% 4.40/1.87  MUC search           : 0.00
% 4.40/1.87  Cooper               : 0.00
% 4.40/1.87  Total                : 1.07
% 4.40/1.87  Index Insertion      : 0.00
% 4.40/1.87  Index Deletion       : 0.00
% 4.40/1.87  Index Matching       : 0.00
% 4.40/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
