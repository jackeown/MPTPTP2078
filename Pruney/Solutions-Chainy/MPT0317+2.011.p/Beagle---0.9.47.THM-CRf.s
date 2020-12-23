%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:01 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 169 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  129 ( 300 expanded)
%              Number of equality atoms :   26 (  84 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_50,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_7' != '#skF_9'
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_80,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_226,plain,(
    ! [B_73,D_74,A_75,C_76] :
      ( r2_hidden(B_73,D_74)
      | ~ r2_hidden(k4_tarski(A_75,B_73),k2_zfmisc_1(C_76,D_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_235,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_80,c_226])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(k1_tarski(A_22),k1_tarski(B_23)) = k1_tarski(A_22)
      | B_23 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_184,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden(A_62,B_63)
      | k4_xboole_0(k1_tarski(A_62),B_63) != k1_tarski(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_192,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden(A_22,k1_tarski(B_23))
      | B_23 = A_22 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_184])).

tff(c_241,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_235,c_192])).

tff(c_244,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_9'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_80])).

tff(c_260,plain,(
    ! [A_80,C_81,B_82,D_83] :
      ( r2_hidden(A_80,C_81)
      | ~ r2_hidden(k4_tarski(A_80,B_82),k2_zfmisc_1(C_81,D_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_263,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_244,c_260])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_263])).

tff(c_272,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_58,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_300,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_300])).

tff(c_321,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_277,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_1'(A_84,B_85),A_84)
      | r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_283,plain,(
    ! [A_86] : r1_tarski(A_86,A_86) ),
    inference(resolution,[status(thm)],[c_277,c_4])).

tff(c_10,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_70,plain,(
    ! [B_33,C_34,A_35] :
      ( r2_hidden(B_33,C_34)
      | ~ r1_tarski(k2_tarski(A_35,B_33),C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_73,plain,(
    ! [A_8,C_34] :
      ( r2_hidden(A_8,C_34)
      | ~ r1_tarski(k1_tarski(A_8),C_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_70])).

tff(c_297,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(resolution,[status(thm)],[c_283,c_73])).

tff(c_537,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( r2_hidden(k4_tarski(A_155,B_156),k2_zfmisc_1(C_157,D_158))
      | ~ r2_hidden(B_156,D_158)
      | ~ r2_hidden(A_155,C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_322,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_271,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_405,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_3')))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_54])).

tff(c_406,plain,(
    ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_322,c_405])).

tff(c_554,plain,
    ( ~ r2_hidden('#skF_3',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_537,c_406])).

tff(c_567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_297,c_554])).

tff(c_569,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_568,plain,
    ( '#skF_7' != '#skF_9'
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_570,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_568])).

tff(c_612,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_749,plain,(
    ! [B_201,D_202,A_203,C_204] :
      ( r2_hidden(B_201,D_202)
      | ~ r2_hidden(k4_tarski(A_203,B_201),k2_zfmisc_1(C_204,D_202)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_758,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_612,c_749])).

tff(c_694,plain,(
    ! [A_190,B_191] :
      ( ~ r2_hidden(A_190,B_191)
      | k4_xboole_0(k1_tarski(A_190),B_191) != k1_tarski(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_701,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden(A_22,k1_tarski(B_23))
      | B_23 = A_22 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_694])).

tff(c_761,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_758,c_701])).

tff(c_767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_761])).

tff(c_769,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_779,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_769,c_779])).

tff(c_790,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_584,plain,(
    ! [A_170,B_171] :
      ( r2_hidden('#skF_1'(A_170,B_171),A_170)
      | r1_tarski(A_170,B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_590,plain,(
    ! [A_172] : r1_tarski(A_172,A_172) ),
    inference(resolution,[status(thm)],[c_584,c_4])).

tff(c_574,plain,(
    ! [B_160,C_161,A_162] :
      ( r2_hidden(B_160,C_161)
      | ~ r1_tarski(k2_tarski(A_162,B_160),C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_577,plain,(
    ! [A_8,C_161] :
      ( r2_hidden(A_8,C_161)
      | ~ r1_tarski(k1_tarski(A_8),C_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_574])).

tff(c_604,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(resolution,[status(thm)],[c_590,c_577])).

tff(c_1046,plain,(
    ! [A_273,B_274,C_275,D_276] :
      ( r2_hidden(k4_tarski(A_273,B_274),k2_zfmisc_1(C_275,D_276))
      | ~ r2_hidden(B_274,D_276)
      | ~ r2_hidden(A_273,C_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_768,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_910,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_3')))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_54])).

tff(c_911,plain,(
    ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_769,c_910])).

tff(c_1063,plain,
    ( ~ r2_hidden('#skF_3',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_1046,c_911])).

tff(c_1076,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_604,c_1063])).

tff(c_1078,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_568])).

tff(c_52,plain,
    ( r2_hidden('#skF_2','#skF_4')
    | '#skF_7' != '#skF_9'
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1089,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_1078,c_52])).

tff(c_1100,plain,(
    ! [A_288,B_289] :
      ( r2_hidden('#skF_1'(A_288,B_289),A_288)
      | r1_tarski(A_288,B_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1115,plain,(
    ! [A_292] : r1_tarski(A_292,A_292) ),
    inference(resolution,[status(thm)],[c_1100,c_4])).

tff(c_1090,plain,(
    ! [A_278,C_279,B_280] :
      ( r2_hidden(A_278,C_279)
      | ~ r1_tarski(k2_tarski(A_278,B_280),C_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1093,plain,(
    ! [A_8,C_279] :
      ( r2_hidden(A_8,C_279)
      | ~ r1_tarski(k1_tarski(A_8),C_279) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1090])).

tff(c_1129,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(resolution,[status(thm)],[c_1115,c_1093])).

tff(c_1351,plain,(
    ! [A_350,B_351,C_352,D_353] :
      ( r2_hidden(k4_tarski(A_350,B_351),k2_zfmisc_1(C_352,D_353))
      | ~ r2_hidden(B_351,D_353)
      | ~ r2_hidden(A_350,C_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1077,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_568])).

tff(c_48,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))
    | '#skF_7' != '#skF_9'
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1302,plain,(
    ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1('#skF_4',k1_tarski('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_1078,c_1077,c_48])).

tff(c_1362,plain,
    ( ~ r2_hidden('#skF_3',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_1351,c_1302])).

tff(c_1376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1129,c_1362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:14:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.59  
% 3.27/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.59  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 3.27/1.59  
% 3.27/1.59  %Foreground sorts:
% 3.27/1.59  
% 3.27/1.59  
% 3.27/1.59  %Background operators:
% 3.27/1.59  
% 3.27/1.59  
% 3.27/1.59  %Foreground operators:
% 3.27/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.27/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.27/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.27/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.27/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.27/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.27/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.27/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.27/1.59  
% 3.27/1.61  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 3.27/1.61  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 3.27/1.61  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.27/1.61  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.27/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.27/1.61  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.27/1.61  tff(f_76, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.27/1.61  tff(c_50, plain, ('#skF_5'='#skF_3' | '#skF_7'!='#skF_9' | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.27/1.61  tff(c_68, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_50])).
% 3.27/1.61  tff(c_56, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.27/1.61  tff(c_80, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_56])).
% 3.27/1.61  tff(c_226, plain, (![B_73, D_74, A_75, C_76]: (r2_hidden(B_73, D_74) | ~r2_hidden(k4_tarski(A_75, B_73), k2_zfmisc_1(C_76, D_74)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.61  tff(c_235, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_80, c_226])).
% 3.27/1.61  tff(c_34, plain, (![A_22, B_23]: (k4_xboole_0(k1_tarski(A_22), k1_tarski(B_23))=k1_tarski(A_22) | B_23=A_22)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.27/1.61  tff(c_184, plain, (![A_62, B_63]: (~r2_hidden(A_62, B_63) | k4_xboole_0(k1_tarski(A_62), B_63)!=k1_tarski(A_62))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.61  tff(c_192, plain, (![A_22, B_23]: (~r2_hidden(A_22, k1_tarski(B_23)) | B_23=A_22)), inference(superposition, [status(thm), theory('equality')], [c_34, c_184])).
% 3.27/1.61  tff(c_241, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_235, c_192])).
% 3.27/1.61  tff(c_244, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_9'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_80])).
% 3.27/1.61  tff(c_260, plain, (![A_80, C_81, B_82, D_83]: (r2_hidden(A_80, C_81) | ~r2_hidden(k4_tarski(A_80, B_82), k2_zfmisc_1(C_81, D_83)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.61  tff(c_263, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_244, c_260])).
% 3.27/1.61  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_263])).
% 3.27/1.61  tff(c_272, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_56])).
% 3.27/1.61  tff(c_58, plain, (r2_hidden('#skF_2', '#skF_4') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.27/1.61  tff(c_300, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_58])).
% 3.27/1.61  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_300])).
% 3.27/1.61  tff(c_321, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 3.27/1.61  tff(c_277, plain, (![A_84, B_85]: (r2_hidden('#skF_1'(A_84, B_85), A_84) | r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.61  tff(c_283, plain, (![A_86]: (r1_tarski(A_86, A_86))), inference(resolution, [status(thm)], [c_277, c_4])).
% 3.27/1.61  tff(c_10, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.27/1.61  tff(c_70, plain, (![B_33, C_34, A_35]: (r2_hidden(B_33, C_34) | ~r1_tarski(k2_tarski(A_35, B_33), C_34))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.27/1.61  tff(c_73, plain, (![A_8, C_34]: (r2_hidden(A_8, C_34) | ~r1_tarski(k1_tarski(A_8), C_34))), inference(superposition, [status(thm), theory('equality')], [c_10, c_70])).
% 3.27/1.61  tff(c_297, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(resolution, [status(thm)], [c_283, c_73])).
% 3.27/1.61  tff(c_537, plain, (![A_155, B_156, C_157, D_158]: (r2_hidden(k4_tarski(A_155, B_156), k2_zfmisc_1(C_157, D_158)) | ~r2_hidden(B_156, D_158) | ~r2_hidden(A_155, C_157))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.61  tff(c_322, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_58])).
% 3.27/1.61  tff(c_271, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_56])).
% 3.27/1.61  tff(c_54, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.27/1.61  tff(c_405, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_3'))) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_54])).
% 3.27/1.61  tff(c_406, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_322, c_405])).
% 3.27/1.61  tff(c_554, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3')) | ~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_537, c_406])).
% 3.27/1.61  tff(c_567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_321, c_297, c_554])).
% 3.27/1.61  tff(c_569, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 3.27/1.61  tff(c_568, plain, ('#skF_7'!='#skF_9' | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 3.27/1.61  tff(c_570, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_568])).
% 3.27/1.61  tff(c_612, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_56])).
% 3.27/1.61  tff(c_749, plain, (![B_201, D_202, A_203, C_204]: (r2_hidden(B_201, D_202) | ~r2_hidden(k4_tarski(A_203, B_201), k2_zfmisc_1(C_204, D_202)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.61  tff(c_758, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_612, c_749])).
% 3.27/1.61  tff(c_694, plain, (![A_190, B_191]: (~r2_hidden(A_190, B_191) | k4_xboole_0(k1_tarski(A_190), B_191)!=k1_tarski(A_190))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.61  tff(c_701, plain, (![A_22, B_23]: (~r2_hidden(A_22, k1_tarski(B_23)) | B_23=A_22)), inference(superposition, [status(thm), theory('equality')], [c_34, c_694])).
% 3.27/1.61  tff(c_761, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_758, c_701])).
% 3.27/1.61  tff(c_767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_570, c_761])).
% 3.27/1.61  tff(c_769, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_56])).
% 3.27/1.61  tff(c_779, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_58])).
% 3.27/1.61  tff(c_789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_769, c_779])).
% 3.27/1.61  tff(c_790, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 3.27/1.61  tff(c_584, plain, (![A_170, B_171]: (r2_hidden('#skF_1'(A_170, B_171), A_170) | r1_tarski(A_170, B_171))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.61  tff(c_590, plain, (![A_172]: (r1_tarski(A_172, A_172))), inference(resolution, [status(thm)], [c_584, c_4])).
% 3.27/1.61  tff(c_574, plain, (![B_160, C_161, A_162]: (r2_hidden(B_160, C_161) | ~r1_tarski(k2_tarski(A_162, B_160), C_161))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.27/1.61  tff(c_577, plain, (![A_8, C_161]: (r2_hidden(A_8, C_161) | ~r1_tarski(k1_tarski(A_8), C_161))), inference(superposition, [status(thm), theory('equality')], [c_10, c_574])).
% 3.27/1.61  tff(c_604, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(resolution, [status(thm)], [c_590, c_577])).
% 3.27/1.61  tff(c_1046, plain, (![A_273, B_274, C_275, D_276]: (r2_hidden(k4_tarski(A_273, B_274), k2_zfmisc_1(C_275, D_276)) | ~r2_hidden(B_274, D_276) | ~r2_hidden(A_273, C_275))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.61  tff(c_768, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_56])).
% 3.27/1.61  tff(c_910, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_3'))) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_768, c_54])).
% 3.27/1.61  tff(c_911, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_769, c_910])).
% 3.27/1.61  tff(c_1063, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3')) | ~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_1046, c_911])).
% 3.27/1.61  tff(c_1076, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_790, c_604, c_1063])).
% 3.27/1.61  tff(c_1078, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_568])).
% 3.27/1.61  tff(c_52, plain, (r2_hidden('#skF_2', '#skF_4') | '#skF_7'!='#skF_9' | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.27/1.61  tff(c_1089, plain, (r2_hidden('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_569, c_1078, c_52])).
% 3.27/1.61  tff(c_1100, plain, (![A_288, B_289]: (r2_hidden('#skF_1'(A_288, B_289), A_288) | r1_tarski(A_288, B_289))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.61  tff(c_1115, plain, (![A_292]: (r1_tarski(A_292, A_292))), inference(resolution, [status(thm)], [c_1100, c_4])).
% 3.27/1.61  tff(c_1090, plain, (![A_278, C_279, B_280]: (r2_hidden(A_278, C_279) | ~r1_tarski(k2_tarski(A_278, B_280), C_279))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.27/1.61  tff(c_1093, plain, (![A_8, C_279]: (r2_hidden(A_8, C_279) | ~r1_tarski(k1_tarski(A_8), C_279))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1090])).
% 3.27/1.61  tff(c_1129, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(resolution, [status(thm)], [c_1115, c_1093])).
% 3.27/1.61  tff(c_1351, plain, (![A_350, B_351, C_352, D_353]: (r2_hidden(k4_tarski(A_350, B_351), k2_zfmisc_1(C_352, D_353)) | ~r2_hidden(B_351, D_353) | ~r2_hidden(A_350, C_352))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.61  tff(c_1077, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_568])).
% 3.27/1.61  tff(c_48, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))) | '#skF_7'!='#skF_9' | ~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.27/1.61  tff(c_1302, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1('#skF_4', k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_1078, c_1077, c_48])).
% 3.27/1.61  tff(c_1362, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3')) | ~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_1351, c_1302])).
% 3.27/1.61  tff(c_1376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1129, c_1362])).
% 3.27/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.61  
% 3.27/1.61  Inference rules
% 3.27/1.61  ----------------------
% 3.27/1.61  #Ref     : 0
% 3.27/1.61  #Sup     : 289
% 3.27/1.61  #Fact    : 0
% 3.27/1.61  #Define  : 0
% 3.27/1.61  #Split   : 6
% 3.27/1.61  #Chain   : 0
% 3.27/1.61  #Close   : 0
% 3.27/1.61  
% 3.27/1.61  Ordering : KBO
% 3.27/1.61  
% 3.27/1.61  Simplification rules
% 3.27/1.61  ----------------------
% 3.27/1.61  #Subsume      : 44
% 3.27/1.61  #Demod        : 57
% 3.27/1.61  #Tautology    : 142
% 3.27/1.61  #SimpNegUnit  : 6
% 3.27/1.61  #BackRed      : 2
% 3.27/1.61  
% 3.27/1.61  #Partial instantiations: 0
% 3.27/1.61  #Strategies tried      : 1
% 3.27/1.61  
% 3.27/1.61  Timing (in seconds)
% 3.27/1.61  ----------------------
% 3.27/1.61  Preprocessing        : 0.33
% 3.27/1.61  Parsing              : 0.18
% 3.27/1.61  CNF conversion       : 0.03
% 3.27/1.61  Main loop            : 0.45
% 3.27/1.61  Inferencing          : 0.18
% 3.27/1.61  Reduction            : 0.12
% 3.27/1.61  Demodulation         : 0.09
% 3.27/1.61  BG Simplification    : 0.02
% 3.27/1.61  Subsumption          : 0.08
% 3.27/1.61  Abstraction          : 0.02
% 3.27/1.61  MUC search           : 0.00
% 3.27/1.61  Cooper               : 0.00
% 3.27/1.61  Total                : 0.82
% 3.27/1.61  Index Insertion      : 0.00
% 3.27/1.61  Index Deletion       : 0.00
% 3.27/1.61  Index Matching       : 0.00
% 3.27/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
