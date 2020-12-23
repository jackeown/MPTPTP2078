%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:14 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 162 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :    6
%              Number of atoms          :  104 ( 273 expanded)
%              Number of equality atoms :   34 (  90 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
      <=> ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_12,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_193,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_170,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_416,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_xboole_0(k2_tarski(A_70,C_71),B_72)
      | r2_hidden(C_71,B_72)
      | r2_hidden(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_552,plain,(
    ! [A_97,C_98,B_99] :
      ( k4_xboole_0(k2_tarski(A_97,C_98),B_99) = k2_tarski(A_97,C_98)
      | r2_hidden(C_98,B_99)
      | r2_hidden(A_97,B_99) ) ),
    inference(resolution,[status(thm)],[c_416,c_4])).

tff(c_28,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_485,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_558,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_485])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_170,c_558])).

tff(c_585,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_587,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_586,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_34,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_762,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [A_44,C_45,B_46] :
      ( ~ r2_hidden(A_44,C_45)
      | ~ r1_xboole_0(k2_tarski(A_44,B_46),C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_448,plain,(
    ! [A_77,B_78,B_79] :
      ( ~ r2_hidden(A_77,B_78)
      | k4_xboole_0(k2_tarski(A_77,B_79),B_78) != k2_tarski(A_77,B_79) ) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_451,plain,(
    ! [A_10,B_78,B_11] :
      ( ~ r2_hidden(A_10,B_78)
      | k4_xboole_0(k2_tarski(B_11,A_10),B_78) != k2_tarski(A_10,B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_448])).

tff(c_769,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_4') != k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_451])).

tff(c_782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_587,c_769])).

tff(c_783,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_913,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_34])).

tff(c_181,plain,(
    ! [A_53,C_54,B_55] :
      ( ~ r2_hidden(A_53,C_54)
      | ~ r1_xboole_0(k2_tarski(B_55,A_53),C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_102])).

tff(c_455,plain,(
    ! [A_80,B_81,B_82] :
      ( ~ r2_hidden(A_80,B_81)
      | k4_xboole_0(k2_tarski(B_82,A_80),B_81) != k2_tarski(B_82,A_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_461,plain,(
    ! [A_10,B_81,B_11] :
      ( ~ r2_hidden(A_10,B_81)
      | k4_xboole_0(k2_tarski(A_10,B_11),B_81) != k2_tarski(B_11,A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_455])).

tff(c_920,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | k2_tarski('#skF_5','#skF_4') != k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_913,c_461])).

tff(c_940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_783,c_920])).

tff(c_941,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_943,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_941])).

tff(c_942,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_945,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_38])).

tff(c_1205,plain,(
    ! [A_133,B_134,B_135] :
      ( ~ r2_hidden(A_133,B_134)
      | k4_xboole_0(k2_tarski(A_133,B_135),B_134) != k2_tarski(A_133,B_135) ) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_1225,plain,(
    ! [B_141,B_142,A_143] :
      ( ~ r2_hidden(B_141,B_142)
      | k4_xboole_0(k2_tarski(A_143,B_141),B_142) != k2_tarski(B_141,A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1205])).

tff(c_1228,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_4') != k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_1225])).

tff(c_1237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_943,c_1228])).

tff(c_1238,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_941])).

tff(c_1241,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_38])).

tff(c_1501,plain,(
    ! [A_165,B_166,B_167] :
      ( ~ r2_hidden(A_165,B_166)
      | k4_xboole_0(k2_tarski(A_165,B_167),B_166) != k2_tarski(A_165,B_167) ) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_1504,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_1501])).

tff(c_1514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_1504])).

tff(c_1515,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1517,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1515])).

tff(c_1516,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1654,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_36])).

tff(c_1802,plain,(
    ! [A_194,B_195,B_196] :
      ( ~ r2_hidden(A_194,B_195)
      | k4_xboole_0(k2_tarski(A_194,B_196),B_195) != k2_tarski(A_194,B_196) ) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_1814,plain,(
    ! [B_197,B_198,A_199] :
      ( ~ r2_hidden(B_197,B_198)
      | k4_xboole_0(k2_tarski(A_199,B_197),B_198) != k2_tarski(B_197,A_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1802])).

tff(c_1817,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_4') != k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1654,c_1814])).

tff(c_1826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1517,c_1817])).

tff(c_1827,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1515])).

tff(c_1965,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_36])).

tff(c_2116,plain,(
    ! [A_226,B_227,B_228] :
      ( ~ r2_hidden(A_226,B_227)
      | k4_xboole_0(k2_tarski(A_226,B_228),B_227) != k2_tarski(A_226,B_228) ) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_2119,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1965,c_2116])).

tff(c_2129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1827,c_2119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.56  
% 3.42/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.57  %$ r2_hidden > r1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.57/1.57  
% 3.57/1.57  %Foreground sorts:
% 3.57/1.57  
% 3.57/1.57  
% 3.57/1.57  %Background operators:
% 3.57/1.57  
% 3.57/1.57  
% 3.57/1.57  %Foreground operators:
% 3.57/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.57/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.57/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.57/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.57/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.57/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.57/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.57/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.57/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.57/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.57/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.57/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.57/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.57/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.57/1.57  
% 3.57/1.58  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.57/1.58  tff(f_71, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 3.57/1.58  tff(f_62, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 3.57/1.58  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.57/1.58  tff(f_52, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.57/1.58  tff(c_12, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.57/1.58  tff(c_32, plain, (~r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.58  tff(c_193, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 3.57/1.58  tff(c_30, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.58  tff(c_170, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 3.57/1.58  tff(c_416, plain, (![A_70, C_71, B_72]: (r1_xboole_0(k2_tarski(A_70, C_71), B_72) | r2_hidden(C_71, B_72) | r2_hidden(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.57/1.58  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.58  tff(c_552, plain, (![A_97, C_98, B_99]: (k4_xboole_0(k2_tarski(A_97, C_98), B_99)=k2_tarski(A_97, C_98) | r2_hidden(C_98, B_99) | r2_hidden(A_97, B_99))), inference(resolution, [status(thm)], [c_416, c_4])).
% 3.57/1.58  tff(c_28, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.58  tff(c_485, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 3.57/1.58  tff(c_558, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_552, c_485])).
% 3.57/1.58  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_170, c_558])).
% 3.57/1.58  tff(c_585, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_28])).
% 3.57/1.58  tff(c_587, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_585])).
% 3.57/1.58  tff(c_586, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 3.57/1.58  tff(c_34, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.58  tff(c_762, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_586, c_34])).
% 3.57/1.58  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k4_xboole_0(A_3, B_4)!=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.58  tff(c_102, plain, (![A_44, C_45, B_46]: (~r2_hidden(A_44, C_45) | ~r1_xboole_0(k2_tarski(A_44, B_46), C_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.57/1.58  tff(c_448, plain, (![A_77, B_78, B_79]: (~r2_hidden(A_77, B_78) | k4_xboole_0(k2_tarski(A_77, B_79), B_78)!=k2_tarski(A_77, B_79))), inference(resolution, [status(thm)], [c_6, c_102])).
% 3.57/1.58  tff(c_451, plain, (![A_10, B_78, B_11]: (~r2_hidden(A_10, B_78) | k4_xboole_0(k2_tarski(B_11, A_10), B_78)!=k2_tarski(A_10, B_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_448])).
% 3.57/1.58  tff(c_769, plain, (~r2_hidden('#skF_5', '#skF_6') | k2_tarski('#skF_5', '#skF_4')!=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_762, c_451])).
% 3.57/1.58  tff(c_782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_587, c_769])).
% 3.57/1.58  tff(c_783, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_585])).
% 3.57/1.58  tff(c_913, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_586, c_34])).
% 3.57/1.58  tff(c_181, plain, (![A_53, C_54, B_55]: (~r2_hidden(A_53, C_54) | ~r1_xboole_0(k2_tarski(B_55, A_53), C_54))), inference(superposition, [status(thm), theory('equality')], [c_12, c_102])).
% 3.57/1.58  tff(c_455, plain, (![A_80, B_81, B_82]: (~r2_hidden(A_80, B_81) | k4_xboole_0(k2_tarski(B_82, A_80), B_81)!=k2_tarski(B_82, A_80))), inference(resolution, [status(thm)], [c_6, c_181])).
% 3.57/1.58  tff(c_461, plain, (![A_10, B_81, B_11]: (~r2_hidden(A_10, B_81) | k4_xboole_0(k2_tarski(A_10, B_11), B_81)!=k2_tarski(B_11, A_10))), inference(superposition, [status(thm), theory('equality')], [c_12, c_455])).
% 3.57/1.58  tff(c_920, plain, (~r2_hidden('#skF_4', '#skF_6') | k2_tarski('#skF_5', '#skF_4')!=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_913, c_461])).
% 3.57/1.58  tff(c_940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_783, c_920])).
% 3.57/1.58  tff(c_941, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 3.57/1.58  tff(c_943, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_941])).
% 3.57/1.58  tff(c_942, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 3.57/1.58  tff(c_38, plain, (~r2_hidden('#skF_1', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.58  tff(c_945, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_942, c_38])).
% 3.57/1.58  tff(c_1205, plain, (![A_133, B_134, B_135]: (~r2_hidden(A_133, B_134) | k4_xboole_0(k2_tarski(A_133, B_135), B_134)!=k2_tarski(A_133, B_135))), inference(resolution, [status(thm)], [c_6, c_102])).
% 3.57/1.58  tff(c_1225, plain, (![B_141, B_142, A_143]: (~r2_hidden(B_141, B_142) | k4_xboole_0(k2_tarski(A_143, B_141), B_142)!=k2_tarski(B_141, A_143))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1205])).
% 3.57/1.58  tff(c_1228, plain, (~r2_hidden('#skF_5', '#skF_6') | k2_tarski('#skF_5', '#skF_4')!=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_945, c_1225])).
% 3.57/1.58  tff(c_1237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_943, c_1228])).
% 3.57/1.58  tff(c_1238, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_941])).
% 3.57/1.58  tff(c_1241, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_942, c_38])).
% 3.57/1.58  tff(c_1501, plain, (![A_165, B_166, B_167]: (~r2_hidden(A_165, B_166) | k4_xboole_0(k2_tarski(A_165, B_167), B_166)!=k2_tarski(A_165, B_167))), inference(resolution, [status(thm)], [c_6, c_102])).
% 3.57/1.58  tff(c_1504, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1241, c_1501])).
% 3.57/1.58  tff(c_1514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1238, c_1504])).
% 3.57/1.58  tff(c_1515, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 3.57/1.58  tff(c_1517, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_1515])).
% 3.57/1.58  tff(c_1516, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 3.57/1.58  tff(c_36, plain, (~r2_hidden('#skF_2', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.58  tff(c_1654, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_36])).
% 3.57/1.58  tff(c_1802, plain, (![A_194, B_195, B_196]: (~r2_hidden(A_194, B_195) | k4_xboole_0(k2_tarski(A_194, B_196), B_195)!=k2_tarski(A_194, B_196))), inference(resolution, [status(thm)], [c_6, c_102])).
% 3.57/1.58  tff(c_1814, plain, (![B_197, B_198, A_199]: (~r2_hidden(B_197, B_198) | k4_xboole_0(k2_tarski(A_199, B_197), B_198)!=k2_tarski(B_197, A_199))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1802])).
% 3.57/1.58  tff(c_1817, plain, (~r2_hidden('#skF_5', '#skF_6') | k2_tarski('#skF_5', '#skF_4')!=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1654, c_1814])).
% 3.57/1.58  tff(c_1826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1517, c_1817])).
% 3.57/1.58  tff(c_1827, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_1515])).
% 3.57/1.58  tff(c_1965, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_36])).
% 3.57/1.58  tff(c_2116, plain, (![A_226, B_227, B_228]: (~r2_hidden(A_226, B_227) | k4_xboole_0(k2_tarski(A_226, B_228), B_227)!=k2_tarski(A_226, B_228))), inference(resolution, [status(thm)], [c_6, c_102])).
% 3.57/1.58  tff(c_2119, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1965, c_2116])).
% 3.57/1.58  tff(c_2129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1827, c_2119])).
% 3.57/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.58  
% 3.57/1.58  Inference rules
% 3.57/1.58  ----------------------
% 3.57/1.58  #Ref     : 0
% 3.57/1.58  #Sup     : 518
% 3.57/1.58  #Fact    : 0
% 3.57/1.58  #Define  : 0
% 3.57/1.58  #Split   : 8
% 3.57/1.58  #Chain   : 0
% 3.57/1.58  #Close   : 0
% 3.57/1.58  
% 3.57/1.58  Ordering : KBO
% 3.57/1.58  
% 3.57/1.58  Simplification rules
% 3.57/1.58  ----------------------
% 3.57/1.58  #Subsume      : 38
% 3.57/1.58  #Demod        : 199
% 3.57/1.58  #Tautology    : 236
% 3.57/1.58  #SimpNegUnit  : 6
% 3.57/1.58  #BackRed      : 0
% 3.57/1.58  
% 3.57/1.58  #Partial instantiations: 0
% 3.57/1.58  #Strategies tried      : 1
% 3.57/1.58  
% 3.57/1.58  Timing (in seconds)
% 3.57/1.58  ----------------------
% 3.57/1.58  Preprocessing        : 0.30
% 3.57/1.58  Parsing              : 0.16
% 3.57/1.58  CNF conversion       : 0.02
% 3.57/1.58  Main loop            : 0.52
% 3.57/1.59  Inferencing          : 0.19
% 3.57/1.59  Reduction            : 0.19
% 3.57/1.59  Demodulation         : 0.15
% 3.57/1.59  BG Simplification    : 0.03
% 3.57/1.59  Subsumption          : 0.07
% 3.57/1.59  Abstraction          : 0.04
% 3.57/1.59  MUC search           : 0.00
% 3.57/1.59  Cooper               : 0.00
% 3.57/1.59  Total                : 0.85
% 3.57/1.59  Index Insertion      : 0.00
% 3.57/1.59  Index Deletion       : 0.00
% 3.57/1.59  Index Matching       : 0.00
% 3.57/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
