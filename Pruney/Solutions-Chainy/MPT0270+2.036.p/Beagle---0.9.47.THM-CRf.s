%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:57 EST 2020

% Result     : Theorem 5.28s
% Output     : CNFRefutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 120 expanded)
%              Number of leaves         :   29 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :  103 ( 192 expanded)
%              Number of equality atoms :   18 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_87,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_137,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(k1_tarski(A_47),B_48)
      | r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_224,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(k1_tarski(A_65),B_66) = k1_tarski(A_65)
      | r2_hidden(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_137,c_40])).

tff(c_60,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_127,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_234,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_127])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_234])).

tff(c_255,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_36,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_532,plain,(
    ! [A_104,C_105,B_106] :
      ( r2_hidden(A_104,C_105)
      | ~ r2_hidden(A_104,B_106)
      | r2_hidden(A_104,k5_xboole_0(B_106,C_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_749,plain,(
    ! [A_127,A_128,B_129] :
      ( r2_hidden(A_127,k3_xboole_0(A_128,B_129))
      | ~ r2_hidden(A_127,A_128)
      | r2_hidden(A_127,k4_xboole_0(A_128,B_129)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_532])).

tff(c_56,plain,(
    ! [C_33,B_32] : ~ r2_hidden(C_33,k4_xboole_0(B_32,k1_tarski(C_33))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_774,plain,(
    ! [A_130,A_131] :
      ( r2_hidden(A_130,k3_xboole_0(A_131,k1_tarski(A_130)))
      | ~ r2_hidden(A_130,A_131) ) ),
    inference(resolution,[status(thm)],[c_749,c_56])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_822,plain,(
    ! [A_135,A_136] :
      ( r2_hidden(A_135,k1_tarski(A_135))
      | ~ r2_hidden(A_135,A_136) ) ),
    inference(resolution,[status(thm)],[c_774,c_6])).

tff(c_869,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_255,c_822])).

tff(c_771,plain,(
    ! [A_127,A_128] :
      ( r2_hidden(A_127,k3_xboole_0(A_128,k1_tarski(A_127)))
      | ~ r2_hidden(A_127,A_128) ) ),
    inference(resolution,[status(thm)],[c_749,c_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_256,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_395,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_64])).

tff(c_616,plain,(
    ! [A_119,C_120,B_121] :
      ( ~ r2_hidden(A_119,C_120)
      | ~ r2_hidden(A_119,B_121)
      | ~ r2_hidden(A_119,k5_xboole_0(B_121,C_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1078,plain,(
    ! [A_151,A_152,B_153] :
      ( ~ r2_hidden(A_151,k3_xboole_0(A_152,B_153))
      | ~ r2_hidden(A_151,A_152)
      | ~ r2_hidden(A_151,k4_xboole_0(A_152,B_153)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_616])).

tff(c_1131,plain,(
    ! [A_151] :
      ( ~ r2_hidden(A_151,k3_xboole_0(k1_tarski('#skF_6'),'#skF_7'))
      | ~ r2_hidden(A_151,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_151,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_1078])).

tff(c_1771,plain,(
    ! [A_175] :
      ( ~ r2_hidden(A_175,k3_xboole_0('#skF_7',k1_tarski('#skF_6')))
      | ~ r2_hidden(A_175,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_175,k1_tarski('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1131])).

tff(c_1791,plain,
    ( ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_771,c_1771])).

tff(c_1835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_869,c_1791])).

tff(c_1836,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2249,plain,(
    ! [A_234,C_235,B_236] :
      ( r2_hidden(A_234,C_235)
      | ~ r2_hidden(A_234,B_236)
      | r2_hidden(A_234,k5_xboole_0(B_236,C_235)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2357,plain,(
    ! [A_242,A_243,B_244] :
      ( r2_hidden(A_242,k3_xboole_0(A_243,B_244))
      | ~ r2_hidden(A_242,A_243)
      | r2_hidden(A_242,k4_xboole_0(A_243,B_244)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2249])).

tff(c_2378,plain,(
    ! [A_245,A_246] :
      ( r2_hidden(A_245,k3_xboole_0(A_246,k1_tarski(A_245)))
      | ~ r2_hidden(A_245,A_246) ) ),
    inference(resolution,[status(thm)],[c_2357,c_56])).

tff(c_2426,plain,(
    ! [A_250,A_251] :
      ( r2_hidden(A_250,k1_tarski(A_250))
      | ~ r2_hidden(A_250,A_251) ) ),
    inference(resolution,[status(thm)],[c_2378,c_6])).

tff(c_2476,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1836,c_2426])).

tff(c_2376,plain,(
    ! [A_242,A_243] :
      ( r2_hidden(A_242,k3_xboole_0(A_243,k1_tarski(A_242)))
      | ~ r2_hidden(A_242,A_243) ) ),
    inference(resolution,[status(thm)],[c_2357,c_56])).

tff(c_1837,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1960,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_66])).

tff(c_2153,plain,(
    ! [A_221,C_222,B_223] :
      ( ~ r2_hidden(A_221,C_222)
      | ~ r2_hidden(A_221,B_223)
      | ~ r2_hidden(A_221,k5_xboole_0(B_223,C_222)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2697,plain,(
    ! [A_266,A_267,B_268] :
      ( ~ r2_hidden(A_266,k3_xboole_0(A_267,B_268))
      | ~ r2_hidden(A_266,A_267)
      | ~ r2_hidden(A_266,k4_xboole_0(A_267,B_268)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2153])).

tff(c_2753,plain,(
    ! [A_266] :
      ( ~ r2_hidden(A_266,k3_xboole_0(k1_tarski('#skF_6'),'#skF_7'))
      | ~ r2_hidden(A_266,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_266,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1960,c_2697])).

tff(c_3317,plain,(
    ! [A_289] :
      ( ~ r2_hidden(A_289,k3_xboole_0('#skF_7',k1_tarski('#skF_6')))
      | ~ r2_hidden(A_289,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_289,k1_tarski('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2753])).

tff(c_3337,plain,
    ( ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_2376,c_3317])).

tff(c_3381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1836,c_2476,c_3337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:28:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.28/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/2.06  
% 5.28/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/2.07  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 5.28/2.07  
% 5.28/2.07  %Foreground sorts:
% 5.28/2.07  
% 5.28/2.07  
% 5.28/2.07  %Background operators:
% 5.28/2.07  
% 5.28/2.07  
% 5.28/2.07  %Foreground operators:
% 5.28/2.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.28/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.28/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.28/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.28/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.28/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.28/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.28/2.07  tff('#skF_7', type, '#skF_7': $i).
% 5.28/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.28/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.28/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.28/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.28/2.07  tff('#skF_6', type, '#skF_6': $i).
% 5.28/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.28/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.28/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.28/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.28/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.28/2.07  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.28/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.28/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.28/2.07  
% 5.28/2.08  tff(f_85, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 5.28/2.08  tff(f_72, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.28/2.08  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.28/2.08  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.28/2.08  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.28/2.08  tff(f_79, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 5.28/2.08  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.28/2.08  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.28/2.08  tff(c_62, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.28/2.08  tff(c_87, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_62])).
% 5.28/2.08  tff(c_137, plain, (![A_47, B_48]: (r1_xboole_0(k1_tarski(A_47), B_48) | r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.28/2.08  tff(c_40, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.28/2.08  tff(c_224, plain, (![A_65, B_66]: (k4_xboole_0(k1_tarski(A_65), B_66)=k1_tarski(A_65) | r2_hidden(A_65, B_66))), inference(resolution, [status(thm)], [c_137, c_40])).
% 5.28/2.08  tff(c_60, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.28/2.08  tff(c_127, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 5.28/2.08  tff(c_234, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_224, c_127])).
% 5.28/2.08  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_234])).
% 5.28/2.08  tff(c_255, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_60])).
% 5.28/2.08  tff(c_36, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.28/2.08  tff(c_532, plain, (![A_104, C_105, B_106]: (r2_hidden(A_104, C_105) | ~r2_hidden(A_104, B_106) | r2_hidden(A_104, k5_xboole_0(B_106, C_105)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.28/2.08  tff(c_749, plain, (![A_127, A_128, B_129]: (r2_hidden(A_127, k3_xboole_0(A_128, B_129)) | ~r2_hidden(A_127, A_128) | r2_hidden(A_127, k4_xboole_0(A_128, B_129)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_532])).
% 5.28/2.08  tff(c_56, plain, (![C_33, B_32]: (~r2_hidden(C_33, k4_xboole_0(B_32, k1_tarski(C_33))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.28/2.08  tff(c_774, plain, (![A_130, A_131]: (r2_hidden(A_130, k3_xboole_0(A_131, k1_tarski(A_130))) | ~r2_hidden(A_130, A_131))), inference(resolution, [status(thm)], [c_749, c_56])).
% 5.28/2.08  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.28/2.08  tff(c_822, plain, (![A_135, A_136]: (r2_hidden(A_135, k1_tarski(A_135)) | ~r2_hidden(A_135, A_136))), inference(resolution, [status(thm)], [c_774, c_6])).
% 5.28/2.08  tff(c_869, plain, (r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_255, c_822])).
% 5.28/2.08  tff(c_771, plain, (![A_127, A_128]: (r2_hidden(A_127, k3_xboole_0(A_128, k1_tarski(A_127))) | ~r2_hidden(A_127, A_128))), inference(resolution, [status(thm)], [c_749, c_56])).
% 5.28/2.08  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.28/2.08  tff(c_256, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 5.28/2.08  tff(c_64, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.28/2.08  tff(c_395, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_64])).
% 5.28/2.08  tff(c_616, plain, (![A_119, C_120, B_121]: (~r2_hidden(A_119, C_120) | ~r2_hidden(A_119, B_121) | ~r2_hidden(A_119, k5_xboole_0(B_121, C_120)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.28/2.08  tff(c_1078, plain, (![A_151, A_152, B_153]: (~r2_hidden(A_151, k3_xboole_0(A_152, B_153)) | ~r2_hidden(A_151, A_152) | ~r2_hidden(A_151, k4_xboole_0(A_152, B_153)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_616])).
% 5.28/2.08  tff(c_1131, plain, (![A_151]: (~r2_hidden(A_151, k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')) | ~r2_hidden(A_151, k1_tarski('#skF_6')) | ~r2_hidden(A_151, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_395, c_1078])).
% 5.28/2.08  tff(c_1771, plain, (![A_175]: (~r2_hidden(A_175, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))) | ~r2_hidden(A_175, k1_tarski('#skF_6')) | ~r2_hidden(A_175, k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1131])).
% 5.28/2.08  tff(c_1791, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_771, c_1771])).
% 5.28/2.08  tff(c_1835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_255, c_869, c_1791])).
% 5.28/2.08  tff(c_1836, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 5.28/2.08  tff(c_2249, plain, (![A_234, C_235, B_236]: (r2_hidden(A_234, C_235) | ~r2_hidden(A_234, B_236) | r2_hidden(A_234, k5_xboole_0(B_236, C_235)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.28/2.08  tff(c_2357, plain, (![A_242, A_243, B_244]: (r2_hidden(A_242, k3_xboole_0(A_243, B_244)) | ~r2_hidden(A_242, A_243) | r2_hidden(A_242, k4_xboole_0(A_243, B_244)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2249])).
% 5.28/2.08  tff(c_2378, plain, (![A_245, A_246]: (r2_hidden(A_245, k3_xboole_0(A_246, k1_tarski(A_245))) | ~r2_hidden(A_245, A_246))), inference(resolution, [status(thm)], [c_2357, c_56])).
% 5.28/2.08  tff(c_2426, plain, (![A_250, A_251]: (r2_hidden(A_250, k1_tarski(A_250)) | ~r2_hidden(A_250, A_251))), inference(resolution, [status(thm)], [c_2378, c_6])).
% 5.28/2.08  tff(c_2476, plain, (r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_1836, c_2426])).
% 5.28/2.08  tff(c_2376, plain, (![A_242, A_243]: (r2_hidden(A_242, k3_xboole_0(A_243, k1_tarski(A_242))) | ~r2_hidden(A_242, A_243))), inference(resolution, [status(thm)], [c_2357, c_56])).
% 5.28/2.08  tff(c_1837, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 5.28/2.08  tff(c_66, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.28/2.08  tff(c_1960, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1837, c_66])).
% 5.28/2.08  tff(c_2153, plain, (![A_221, C_222, B_223]: (~r2_hidden(A_221, C_222) | ~r2_hidden(A_221, B_223) | ~r2_hidden(A_221, k5_xboole_0(B_223, C_222)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.28/2.08  tff(c_2697, plain, (![A_266, A_267, B_268]: (~r2_hidden(A_266, k3_xboole_0(A_267, B_268)) | ~r2_hidden(A_266, A_267) | ~r2_hidden(A_266, k4_xboole_0(A_267, B_268)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2153])).
% 5.28/2.08  tff(c_2753, plain, (![A_266]: (~r2_hidden(A_266, k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')) | ~r2_hidden(A_266, k1_tarski('#skF_6')) | ~r2_hidden(A_266, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1960, c_2697])).
% 5.28/2.08  tff(c_3317, plain, (![A_289]: (~r2_hidden(A_289, k3_xboole_0('#skF_7', k1_tarski('#skF_6'))) | ~r2_hidden(A_289, k1_tarski('#skF_6')) | ~r2_hidden(A_289, k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2753])).
% 5.28/2.08  tff(c_3337, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_2376, c_3317])).
% 5.28/2.08  tff(c_3381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1836, c_2476, c_3337])).
% 5.28/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.28/2.08  
% 5.28/2.08  Inference rules
% 5.28/2.08  ----------------------
% 5.28/2.08  #Ref     : 0
% 5.28/2.08  #Sup     : 777
% 5.28/2.08  #Fact    : 0
% 5.28/2.08  #Define  : 0
% 5.28/2.08  #Split   : 2
% 5.28/2.08  #Chain   : 0
% 5.28/2.08  #Close   : 0
% 5.28/2.08  
% 5.28/2.08  Ordering : KBO
% 5.28/2.08  
% 5.28/2.08  Simplification rules
% 5.28/2.08  ----------------------
% 5.28/2.08  #Subsume      : 113
% 5.28/2.08  #Demod        : 85
% 5.28/2.08  #Tautology    : 179
% 5.28/2.08  #SimpNegUnit  : 3
% 5.28/2.08  #BackRed      : 1
% 5.28/2.08  
% 5.28/2.08  #Partial instantiations: 0
% 5.28/2.08  #Strategies tried      : 1
% 5.28/2.08  
% 5.28/2.08  Timing (in seconds)
% 5.28/2.08  ----------------------
% 5.28/2.08  Preprocessing        : 0.33
% 5.28/2.08  Parsing              : 0.17
% 5.28/2.08  CNF conversion       : 0.02
% 5.28/2.08  Main loop            : 0.97
% 5.28/2.08  Inferencing          : 0.35
% 5.28/2.08  Reduction            : 0.29
% 5.28/2.08  Demodulation         : 0.21
% 5.28/2.08  BG Simplification    : 0.05
% 5.28/2.08  Subsumption          : 0.21
% 5.28/2.08  Abstraction          : 0.06
% 5.28/2.08  MUC search           : 0.00
% 5.28/2.08  Cooper               : 0.00
% 5.28/2.08  Total                : 1.34
% 5.28/2.08  Index Insertion      : 0.00
% 5.28/2.08  Index Deletion       : 0.00
% 5.28/2.08  Index Matching       : 0.00
% 5.28/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
