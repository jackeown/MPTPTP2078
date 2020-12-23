%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:14 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 139 expanded)
%              Number of leaves         :   37 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 204 expanded)
%              Number of equality atoms :   62 ( 158 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k2_mcart_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_6 > #skF_15 > #skF_1 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_12 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_98,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
    <=> ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_30,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_927,plain,(
    ! [A_199,B_200] : ~ r2_hidden(A_199,k2_zfmisc_1(A_199,B_200)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_930,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_927])).

tff(c_192,plain,(
    ! [A_92,B_93] : ~ r2_hidden(A_92,k2_zfmisc_1(A_92,B_93)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_195,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_192])).

tff(c_32,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_80,plain,
    ( k2_mcart_1('#skF_13') = '#skF_13'
    | k1_mcart_1('#skF_13') = '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_128,plain,(
    k1_mcart_1('#skF_13') = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_82,plain,(
    k4_tarski('#skF_14','#skF_15') = '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_133,plain,(
    ! [A_83,B_84] : k1_mcart_1(k4_tarski(A_83,B_84)) = A_83 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_142,plain,(
    k1_mcart_1('#skF_13') = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_133])).

tff(c_145,plain,(
    '#skF_14' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_142])).

tff(c_146,plain,(
    k4_tarski('#skF_13','#skF_15') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_82])).

tff(c_74,plain,(
    ! [A_63] :
      ( r2_hidden('#skF_12'(A_63),A_63)
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_380,plain,(
    ! [D_129,B_130,A_131] :
      ( D_129 = B_130
      | D_129 = A_131
      | ~ r2_hidden(D_129,k2_tarski(A_131,B_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_418,plain,(
    ! [D_136,A_137] :
      ( D_136 = A_137
      | D_136 = A_137
      | ~ r2_hidden(D_136,k1_tarski(A_137)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_380])).

tff(c_433,plain,(
    ! [A_137] :
      ( '#skF_12'(k1_tarski(A_137)) = A_137
      | k1_tarski(A_137) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_418])).

tff(c_111,plain,(
    ! [A_81] : k2_tarski(A_81,A_81) = k1_tarski(A_81) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [D_10,A_5] : r2_hidden(D_10,k2_tarski(A_5,D_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [A_81] : r2_hidden(A_81,k1_tarski(A_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_10])).

tff(c_518,plain,(
    ! [C_146,A_147,D_148] :
      ( ~ r2_hidden(C_146,A_147)
      | k4_tarski(C_146,D_148) != '#skF_12'(A_147)
      | k1_xboole_0 = A_147 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_805,plain,(
    ! [A_185,D_186] :
      ( k4_tarski(A_185,D_186) != '#skF_12'(k1_tarski(A_185))
      | k1_tarski(A_185) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_117,c_518])).

tff(c_906,plain,(
    ! [A_197,D_198] :
      ( k4_tarski(A_197,D_198) != A_197
      | k1_tarski(A_197) = k1_xboole_0
      | k1_tarski(A_197) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_805])).

tff(c_910,plain,(
    k1_tarski('#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_906])).

tff(c_302,plain,(
    ! [C_112,D_113] : r2_hidden(k4_tarski(C_112,D_113),k2_zfmisc_1(k1_tarski(C_112),k1_tarski(D_113))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_311,plain,(
    r2_hidden('#skF_13',k2_zfmisc_1(k1_tarski('#skF_13'),k1_tarski('#skF_15'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_302])).

tff(c_915,plain,(
    r2_hidden('#skF_13',k2_zfmisc_1(k1_xboole_0,k1_tarski('#skF_15'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_311])).

tff(c_918,plain,(
    r2_hidden('#skF_13',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_915])).

tff(c_920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_918])).

tff(c_921,plain,(
    k2_mcart_1('#skF_13') = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_952,plain,(
    ! [A_207,B_208] : k2_mcart_1(k4_tarski(A_207,B_208)) = B_208 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_961,plain,(
    k2_mcart_1('#skF_13') = '#skF_15' ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_952])).

tff(c_964,plain,(
    '#skF_15' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_961])).

tff(c_977,plain,(
    k4_tarski('#skF_14','#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_964,c_82])).

tff(c_1057,plain,(
    ! [D_219,B_220,A_221] :
      ( D_219 = B_220
      | D_219 = A_221
      | ~ r2_hidden(D_219,k2_tarski(A_221,B_220)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1557,plain,(
    ! [D_297,A_298] :
      ( D_297 = A_298
      | D_297 = A_298
      | ~ r2_hidden(D_297,k1_tarski(A_298)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1057])).

tff(c_1572,plain,(
    ! [A_298] :
      ( '#skF_12'(k1_tarski(A_298)) = A_298
      | k1_tarski(A_298) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_1557])).

tff(c_1348,plain,(
    ! [D_265,A_266,C_267] :
      ( ~ r2_hidden(D_265,A_266)
      | k4_tarski(C_267,D_265) != '#skF_12'(A_266)
      | k1_xboole_0 = A_266 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1623,plain,(
    ! [C_309,A_310] :
      ( k4_tarski(C_309,A_310) != '#skF_12'(k1_tarski(A_310))
      | k1_tarski(A_310) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_117,c_1348])).

tff(c_1722,plain,(
    ! [C_320,A_321] :
      ( k4_tarski(C_320,A_321) != A_321
      | k1_tarski(A_321) = k1_xboole_0
      | k1_tarski(A_321) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1572,c_1623])).

tff(c_1726,plain,(
    k1_tarski('#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_977,c_1722])).

tff(c_1184,plain,(
    ! [C_241,D_242] : r2_hidden(k4_tarski(C_241,D_242),k2_zfmisc_1(k1_tarski(C_241),k1_tarski(D_242))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1196,plain,(
    r2_hidden('#skF_13',k2_zfmisc_1(k1_tarski('#skF_14'),k1_tarski('#skF_13'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_977,c_1184])).

tff(c_1774,plain,(
    r2_hidden('#skF_13',k2_zfmisc_1(k1_tarski('#skF_14'),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1726,c_1196])).

tff(c_1779,plain,(
    r2_hidden('#skF_13',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1774])).

tff(c_1781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_930,c_1779])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:45:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.70  
% 3.62/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.70  %$ r2_hidden > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k2_mcart_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_6 > #skF_15 > #skF_1 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_12 > #skF_9 > #skF_5 > #skF_4
% 3.62/1.70  
% 3.62/1.70  %Foreground sorts:
% 3.62/1.70  
% 3.62/1.70  
% 3.62/1.70  %Background operators:
% 3.62/1.70  
% 3.62/1.70  
% 3.62/1.70  %Foreground operators:
% 3.62/1.70  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.62/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.62/1.70  tff('#skF_15', type, '#skF_15': $i).
% 3.62/1.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.62/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.62/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.62/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.62/1.70  tff('#skF_14', type, '#skF_14': $i).
% 3.62/1.70  tff('#skF_13', type, '#skF_13': $i).
% 3.62/1.70  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 3.62/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.62/1.70  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.62/1.70  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 3.62/1.70  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.62/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.70  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.62/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.62/1.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.62/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.70  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.62/1.70  tff('#skF_12', type, '#skF_12': $i > $i).
% 3.62/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.62/1.70  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.62/1.70  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.62/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.62/1.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.62/1.70  
% 3.98/1.71  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.98/1.71  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.98/1.71  tff(f_108, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.98/1.71  tff(f_82, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.98/1.71  tff(f_98, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.98/1.71  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.98/1.71  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.98/1.71  tff(f_58, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 3.98/1.71  tff(c_30, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.98/1.71  tff(c_927, plain, (![A_199, B_200]: (~r2_hidden(A_199, k2_zfmisc_1(A_199, B_200)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.98/1.71  tff(c_930, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_927])).
% 3.98/1.71  tff(c_192, plain, (![A_92, B_93]: (~r2_hidden(A_92, k2_zfmisc_1(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.98/1.71  tff(c_195, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_192])).
% 3.98/1.71  tff(c_32, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.98/1.71  tff(c_80, plain, (k2_mcart_1('#skF_13')='#skF_13' | k1_mcart_1('#skF_13')='#skF_13'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.98/1.71  tff(c_128, plain, (k1_mcart_1('#skF_13')='#skF_13'), inference(splitLeft, [status(thm)], [c_80])).
% 3.98/1.71  tff(c_82, plain, (k4_tarski('#skF_14', '#skF_15')='#skF_13'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.98/1.71  tff(c_133, plain, (![A_83, B_84]: (k1_mcart_1(k4_tarski(A_83, B_84))=A_83)), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.98/1.71  tff(c_142, plain, (k1_mcart_1('#skF_13')='#skF_14'), inference(superposition, [status(thm), theory('equality')], [c_82, c_133])).
% 3.98/1.71  tff(c_145, plain, ('#skF_14'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_142])).
% 3.98/1.71  tff(c_146, plain, (k4_tarski('#skF_13', '#skF_15')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_82])).
% 3.98/1.71  tff(c_74, plain, (![A_63]: (r2_hidden('#skF_12'(A_63), A_63) | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.98/1.71  tff(c_26, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.71  tff(c_380, plain, (![D_129, B_130, A_131]: (D_129=B_130 | D_129=A_131 | ~r2_hidden(D_129, k2_tarski(A_131, B_130)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.98/1.71  tff(c_418, plain, (![D_136, A_137]: (D_136=A_137 | D_136=A_137 | ~r2_hidden(D_136, k1_tarski(A_137)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_380])).
% 3.98/1.71  tff(c_433, plain, (![A_137]: ('#skF_12'(k1_tarski(A_137))=A_137 | k1_tarski(A_137)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_418])).
% 3.98/1.71  tff(c_111, plain, (![A_81]: (k2_tarski(A_81, A_81)=k1_tarski(A_81))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.71  tff(c_10, plain, (![D_10, A_5]: (r2_hidden(D_10, k2_tarski(A_5, D_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.98/1.71  tff(c_117, plain, (![A_81]: (r2_hidden(A_81, k1_tarski(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_111, c_10])).
% 3.98/1.71  tff(c_518, plain, (![C_146, A_147, D_148]: (~r2_hidden(C_146, A_147) | k4_tarski(C_146, D_148)!='#skF_12'(A_147) | k1_xboole_0=A_147)), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.98/1.71  tff(c_805, plain, (![A_185, D_186]: (k4_tarski(A_185, D_186)!='#skF_12'(k1_tarski(A_185)) | k1_tarski(A_185)=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_518])).
% 3.98/1.71  tff(c_906, plain, (![A_197, D_198]: (k4_tarski(A_197, D_198)!=A_197 | k1_tarski(A_197)=k1_xboole_0 | k1_tarski(A_197)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_433, c_805])).
% 3.98/1.71  tff(c_910, plain, (k1_tarski('#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_146, c_906])).
% 3.98/1.71  tff(c_302, plain, (![C_112, D_113]: (r2_hidden(k4_tarski(C_112, D_113), k2_zfmisc_1(k1_tarski(C_112), k1_tarski(D_113))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.98/1.71  tff(c_311, plain, (r2_hidden('#skF_13', k2_zfmisc_1(k1_tarski('#skF_13'), k1_tarski('#skF_15')))), inference(superposition, [status(thm), theory('equality')], [c_146, c_302])).
% 3.98/1.71  tff(c_915, plain, (r2_hidden('#skF_13', k2_zfmisc_1(k1_xboole_0, k1_tarski('#skF_15')))), inference(demodulation, [status(thm), theory('equality')], [c_910, c_311])).
% 3.98/1.71  tff(c_918, plain, (r2_hidden('#skF_13', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_915])).
% 3.98/1.71  tff(c_920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_918])).
% 3.98/1.71  tff(c_921, plain, (k2_mcart_1('#skF_13')='#skF_13'), inference(splitRight, [status(thm)], [c_80])).
% 3.98/1.71  tff(c_952, plain, (![A_207, B_208]: (k2_mcart_1(k4_tarski(A_207, B_208))=B_208)), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.98/1.71  tff(c_961, plain, (k2_mcart_1('#skF_13')='#skF_15'), inference(superposition, [status(thm), theory('equality')], [c_82, c_952])).
% 3.98/1.71  tff(c_964, plain, ('#skF_15'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_921, c_961])).
% 3.98/1.71  tff(c_977, plain, (k4_tarski('#skF_14', '#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_964, c_82])).
% 3.98/1.71  tff(c_1057, plain, (![D_219, B_220, A_221]: (D_219=B_220 | D_219=A_221 | ~r2_hidden(D_219, k2_tarski(A_221, B_220)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.98/1.71  tff(c_1557, plain, (![D_297, A_298]: (D_297=A_298 | D_297=A_298 | ~r2_hidden(D_297, k1_tarski(A_298)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1057])).
% 3.98/1.71  tff(c_1572, plain, (![A_298]: ('#skF_12'(k1_tarski(A_298))=A_298 | k1_tarski(A_298)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_1557])).
% 3.98/1.71  tff(c_1348, plain, (![D_265, A_266, C_267]: (~r2_hidden(D_265, A_266) | k4_tarski(C_267, D_265)!='#skF_12'(A_266) | k1_xboole_0=A_266)), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.98/1.71  tff(c_1623, plain, (![C_309, A_310]: (k4_tarski(C_309, A_310)!='#skF_12'(k1_tarski(A_310)) | k1_tarski(A_310)=k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_1348])).
% 3.98/1.71  tff(c_1722, plain, (![C_320, A_321]: (k4_tarski(C_320, A_321)!=A_321 | k1_tarski(A_321)=k1_xboole_0 | k1_tarski(A_321)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1572, c_1623])).
% 3.98/1.71  tff(c_1726, plain, (k1_tarski('#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_977, c_1722])).
% 3.98/1.71  tff(c_1184, plain, (![C_241, D_242]: (r2_hidden(k4_tarski(C_241, D_242), k2_zfmisc_1(k1_tarski(C_241), k1_tarski(D_242))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.98/1.71  tff(c_1196, plain, (r2_hidden('#skF_13', k2_zfmisc_1(k1_tarski('#skF_14'), k1_tarski('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_977, c_1184])).
% 3.98/1.71  tff(c_1774, plain, (r2_hidden('#skF_13', k2_zfmisc_1(k1_tarski('#skF_14'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1726, c_1196])).
% 3.98/1.71  tff(c_1779, plain, (r2_hidden('#skF_13', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1774])).
% 3.98/1.71  tff(c_1781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_930, c_1779])).
% 3.98/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.71  
% 3.98/1.71  Inference rules
% 3.98/1.71  ----------------------
% 3.98/1.71  #Ref     : 0
% 3.98/1.71  #Sup     : 400
% 3.98/1.71  #Fact    : 4
% 3.98/1.71  #Define  : 0
% 3.98/1.71  #Split   : 6
% 3.98/1.71  #Chain   : 0
% 3.98/1.71  #Close   : 0
% 3.98/1.71  
% 3.98/1.71  Ordering : KBO
% 3.98/1.71  
% 3.98/1.71  Simplification rules
% 3.98/1.71  ----------------------
% 3.98/1.71  #Subsume      : 48
% 3.98/1.71  #Demod        : 72
% 3.98/1.71  #Tautology    : 111
% 3.98/1.71  #SimpNegUnit  : 24
% 3.98/1.71  #BackRed      : 18
% 3.98/1.71  
% 3.98/1.71  #Partial instantiations: 0
% 3.98/1.71  #Strategies tried      : 1
% 3.98/1.71  
% 3.98/1.71  Timing (in seconds)
% 3.98/1.71  ----------------------
% 3.98/1.72  Preprocessing        : 0.38
% 3.98/1.72  Parsing              : 0.19
% 3.98/1.72  CNF conversion       : 0.03
% 3.98/1.72  Main loop            : 0.52
% 3.98/1.72  Inferencing          : 0.19
% 3.98/1.72  Reduction            : 0.17
% 3.98/1.72  Demodulation         : 0.11
% 3.98/1.72  BG Simplification    : 0.03
% 3.98/1.72  Subsumption          : 0.09
% 3.98/1.72  Abstraction          : 0.03
% 3.98/1.72  MUC search           : 0.00
% 3.98/1.72  Cooper               : 0.00
% 3.98/1.72  Total                : 0.94
% 3.98/1.72  Index Insertion      : 0.00
% 3.98/1.72  Index Deletion       : 0.00
% 3.98/1.72  Index Matching       : 0.00
% 3.98/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
