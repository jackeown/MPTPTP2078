%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:58 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 175 expanded)
%              Number of leaves         :   27 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  122 ( 321 expanded)
%              Number of equality atoms :   23 (  97 expanded)
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

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

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

tff(c_1066,plain,(
    ! [A_287,B_288] :
      ( r2_hidden('#skF_1'(A_287,B_288),A_287)
      | r1_tarski(A_287,B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1081,plain,(
    ! [A_291] : r1_tarski(A_291,A_291) ),
    inference(resolution,[status(thm)],[c_1066,c_4])).

tff(c_10,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1056,plain,(
    ! [A_277,C_278,B_279] :
      ( r2_hidden(A_277,C_278)
      | ~ r1_tarski(k2_tarski(A_277,B_279),C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1059,plain,(
    ! [A_8,C_278] :
      ( r2_hidden(A_8,C_278)
      | ~ r1_tarski(k1_tarski(A_8),C_278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1056])).

tff(c_1095,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(resolution,[status(thm)],[c_1081,c_1059])).

tff(c_286,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85,B_86),A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_292,plain,(
    ! [A_87] : r1_tarski(A_87,A_87) ),
    inference(resolution,[status(thm)],[c_286,c_4])).

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

tff(c_306,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(resolution,[status(thm)],[c_292,c_73])).

tff(c_52,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r2_hidden('#skF_7','#skF_9')
    | '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_80,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_261,plain,(
    ! [A_81,C_82,B_83,D_84] :
      ( r2_hidden(A_81,C_82)
      | ~ r2_hidden(k4_tarski(A_81,B_83),k2_zfmisc_1(C_82,D_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_270,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_80,c_261])).

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

tff(c_273,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_270,c_192])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_273])).

tff(c_281,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_309,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_309])).

tff(c_330,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_546,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( r2_hidden(k4_tarski(A_156,B_157),k2_zfmisc_1(C_158,D_159))
      | ~ r2_hidden(B_157,D_159)
      | ~ r2_hidden(A_156,C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_331,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_280,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_414,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_54])).

tff(c_415,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_414])).

tff(c_563,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_546,c_415])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_330,c_563])).

tff(c_578,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_597,plain,(
    ! [A_171,B_172] :
      ( r2_hidden('#skF_1'(A_171,B_172),A_171)
      | r1_tarski(A_171,B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_603,plain,(
    ! [A_173] : r1_tarski(A_173,A_173) ),
    inference(resolution,[status(thm)],[c_597,c_4])).

tff(c_587,plain,(
    ! [B_161,C_162,A_163] :
      ( r2_hidden(B_161,C_162)
      | ~ r1_tarski(k2_tarski(A_163,B_161),C_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_590,plain,(
    ! [A_8,C_162] :
      ( r2_hidden(A_8,C_162)
      | ~ r1_tarski(k1_tarski(A_8),C_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_587])).

tff(c_617,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(resolution,[status(thm)],[c_603,c_590])).

tff(c_577,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_583,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_625,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_8','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_58])).

tff(c_626,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_625])).

tff(c_755,plain,(
    ! [B_205,D_206,A_207,C_208] :
      ( r2_hidden(B_205,D_206)
      | ~ r2_hidden(k4_tarski(A_207,B_205),k2_zfmisc_1(C_208,D_206)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_761,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_626,c_755])).

tff(c_767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_761])).

tff(c_769,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(splitRight,[status(thm)],[c_625])).

tff(c_788,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden(k4_tarski('#skF_8','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_56])).

tff(c_789,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_769,c_788])).

tff(c_1019,plain,(
    ! [A_272,B_273,C_274,D_275] :
      ( r2_hidden(k4_tarski(A_272,B_273),k2_zfmisc_1(C_274,D_275))
      | ~ r2_hidden(B_273,D_275)
      | ~ r2_hidden(A_272,C_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_768,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_625])).

tff(c_959,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))
    | r2_hidden(k4_tarski('#skF_8','#skF_7'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_768,c_54])).

tff(c_960,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_769,c_959])).

tff(c_1026,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1019,c_960])).

tff(c_1046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_789,c_1026])).

tff(c_1048,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_50,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_9')
    | '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1055,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_1048,c_50])).

tff(c_1317,plain,(
    ! [A_349,B_350,C_351,D_352] :
      ( r2_hidden(k4_tarski(A_349,B_350),k2_zfmisc_1(C_351,D_352))
      | ~ r2_hidden(B_350,D_352)
      | ~ r2_hidden(A_349,C_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1047,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_48,plain,
    ( ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))
    | ~ r2_hidden('#skF_7','#skF_9')
    | '#skF_6' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1268,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_3'),k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_1048,c_1047,c_48])).

tff(c_1328,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1317,c_1268])).

tff(c_1342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1055,c_1328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.59  
% 3.16/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.59  %$ r2_hidden > r1_tarski > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 3.16/1.59  
% 3.16/1.59  %Foreground sorts:
% 3.16/1.59  
% 3.16/1.59  
% 3.16/1.59  %Background operators:
% 3.16/1.59  
% 3.16/1.59  
% 3.16/1.59  %Foreground operators:
% 3.16/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.16/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.16/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.16/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.16/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.16/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.59  
% 3.16/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.16/1.61  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.16/1.61  tff(f_76, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.16/1.61  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 3.16/1.61  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 3.16/1.61  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.16/1.61  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.16/1.61  tff(c_1066, plain, (![A_287, B_288]: (r2_hidden('#skF_1'(A_287, B_288), A_287) | r1_tarski(A_287, B_288))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.61  tff(c_1081, plain, (![A_291]: (r1_tarski(A_291, A_291))), inference(resolution, [status(thm)], [c_1066, c_4])).
% 3.16/1.61  tff(c_10, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.16/1.61  tff(c_1056, plain, (![A_277, C_278, B_279]: (r2_hidden(A_277, C_278) | ~r1_tarski(k2_tarski(A_277, B_279), C_278))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.61  tff(c_1059, plain, (![A_8, C_278]: (r2_hidden(A_8, C_278) | ~r1_tarski(k1_tarski(A_8), C_278))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1056])).
% 3.16/1.61  tff(c_1095, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(resolution, [status(thm)], [c_1081, c_1059])).
% 3.16/1.61  tff(c_286, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85, B_86), A_85) | r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.61  tff(c_292, plain, (![A_87]: (r1_tarski(A_87, A_87))), inference(resolution, [status(thm)], [c_286, c_4])).
% 3.16/1.61  tff(c_70, plain, (![B_33, C_34, A_35]: (r2_hidden(B_33, C_34) | ~r1_tarski(k2_tarski(A_35, B_33), C_34))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.61  tff(c_73, plain, (![A_8, C_34]: (r2_hidden(A_8, C_34) | ~r1_tarski(k1_tarski(A_8), C_34))), inference(superposition, [status(thm), theory('equality')], [c_10, c_70])).
% 3.16/1.61  tff(c_306, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(resolution, [status(thm)], [c_292, c_73])).
% 3.16/1.61  tff(c_52, plain, ('#skF_2'='#skF_4' | ~r2_hidden('#skF_7', '#skF_9') | '#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.61  tff(c_68, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_52])).
% 3.16/1.61  tff(c_58, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.61  tff(c_80, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(splitLeft, [status(thm)], [c_58])).
% 3.16/1.61  tff(c_261, plain, (![A_81, C_82, B_83, D_84]: (r2_hidden(A_81, C_82) | ~r2_hidden(k4_tarski(A_81, B_83), k2_zfmisc_1(C_82, D_84)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.61  tff(c_270, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_80, c_261])).
% 3.16/1.61  tff(c_34, plain, (![A_22, B_23]: (k4_xboole_0(k1_tarski(A_22), k1_tarski(B_23))=k1_tarski(A_22) | B_23=A_22)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.16/1.61  tff(c_184, plain, (![A_62, B_63]: (~r2_hidden(A_62, B_63) | k4_xboole_0(k1_tarski(A_62), B_63)!=k1_tarski(A_62))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.16/1.61  tff(c_192, plain, (![A_22, B_23]: (~r2_hidden(A_22, k1_tarski(B_23)) | B_23=A_22)), inference(superposition, [status(thm), theory('equality')], [c_34, c_184])).
% 3.16/1.61  tff(c_273, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_270, c_192])).
% 3.16/1.61  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_273])).
% 3.16/1.61  tff(c_281, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_58])).
% 3.16/1.61  tff(c_56, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.61  tff(c_309, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.16/1.61  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_309])).
% 3.16/1.61  tff(c_330, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 3.16/1.61  tff(c_546, plain, (![A_156, B_157, C_158, D_159]: (r2_hidden(k4_tarski(A_156, B_157), k2_zfmisc_1(C_158, D_159)) | ~r2_hidden(B_157, D_159) | ~r2_hidden(A_156, C_158))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.61  tff(c_331, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_56])).
% 3.16/1.61  tff(c_280, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 3.16/1.61  tff(c_54, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.61  tff(c_414, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_54])).
% 3.16/1.61  tff(c_415, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_331, c_414])).
% 3.16/1.61  tff(c_563, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_546, c_415])).
% 3.16/1.61  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_306, c_330, c_563])).
% 3.16/1.61  tff(c_578, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_52])).
% 3.16/1.61  tff(c_597, plain, (![A_171, B_172]: (r2_hidden('#skF_1'(A_171, B_172), A_171) | r1_tarski(A_171, B_172))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.61  tff(c_603, plain, (![A_173]: (r1_tarski(A_173, A_173))), inference(resolution, [status(thm)], [c_597, c_4])).
% 3.16/1.61  tff(c_587, plain, (![B_161, C_162, A_163]: (r2_hidden(B_161, C_162) | ~r1_tarski(k2_tarski(A_163, B_161), C_162))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.61  tff(c_590, plain, (![A_8, C_162]: (r2_hidden(A_8, C_162) | ~r1_tarski(k1_tarski(A_8), C_162))), inference(superposition, [status(thm), theory('equality')], [c_10, c_587])).
% 3.16/1.61  tff(c_617, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(resolution, [status(thm)], [c_603, c_590])).
% 3.16/1.61  tff(c_577, plain, (~r2_hidden('#skF_7', '#skF_9') | '#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_52])).
% 3.16/1.61  tff(c_583, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_577])).
% 3.16/1.61  tff(c_625, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_8', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_58])).
% 3.16/1.61  tff(c_626, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(splitLeft, [status(thm)], [c_625])).
% 3.16/1.61  tff(c_755, plain, (![B_205, D_206, A_207, C_208]: (r2_hidden(B_205, D_206) | ~r2_hidden(k4_tarski(A_207, B_205), k2_zfmisc_1(C_208, D_206)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.61  tff(c_761, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_626, c_755])).
% 3.16/1.61  tff(c_767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_583, c_761])).
% 3.16/1.61  tff(c_769, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(splitRight, [status(thm)], [c_625])).
% 3.16/1.61  tff(c_788, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden(k4_tarski('#skF_8', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_56])).
% 3.16/1.61  tff(c_789, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_769, c_788])).
% 3.16/1.61  tff(c_1019, plain, (![A_272, B_273, C_274, D_275]: (r2_hidden(k4_tarski(A_272, B_273), k2_zfmisc_1(C_274, D_275)) | ~r2_hidden(B_273, D_275) | ~r2_hidden(A_272, C_274))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.61  tff(c_768, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_625])).
% 3.16/1.61  tff(c_959, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')) | r2_hidden(k4_tarski('#skF_8', '#skF_7'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_768, c_54])).
% 3.16/1.61  tff(c_960, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_769, c_959])).
% 3.16/1.61  tff(c_1026, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_1019, c_960])).
% 3.16/1.61  tff(c_1046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_617, c_789, c_1026])).
% 3.16/1.61  tff(c_1048, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_577])).
% 3.16/1.61  tff(c_50, plain, (r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_7', '#skF_9') | '#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.61  tff(c_1055, plain, (r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_578, c_1048, c_50])).
% 3.16/1.61  tff(c_1317, plain, (![A_349, B_350, C_351, D_352]: (r2_hidden(k4_tarski(A_349, B_350), k2_zfmisc_1(C_351, D_352)) | ~r2_hidden(B_350, D_352) | ~r2_hidden(A_349, C_351))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.61  tff(c_1047, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_577])).
% 3.16/1.61  tff(c_48, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')) | ~r2_hidden('#skF_7', '#skF_9') | '#skF_6'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.61  tff(c_1268, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_3'), k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_1048, c_1047, c_48])).
% 3.16/1.61  tff(c_1328, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_1317, c_1268])).
% 3.16/1.61  tff(c_1342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1055, c_1328])).
% 3.16/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.61  
% 3.16/1.61  Inference rules
% 3.16/1.61  ----------------------
% 3.16/1.61  #Ref     : 0
% 3.16/1.61  #Sup     : 278
% 3.16/1.61  #Fact    : 0
% 3.16/1.61  #Define  : 0
% 3.16/1.61  #Split   : 5
% 3.16/1.61  #Chain   : 0
% 3.16/1.61  #Close   : 0
% 3.16/1.61  
% 3.16/1.61  Ordering : KBO
% 3.16/1.61  
% 3.16/1.61  Simplification rules
% 3.16/1.61  ----------------------
% 3.16/1.61  #Subsume      : 40
% 3.16/1.61  #Demod        : 61
% 3.16/1.61  #Tautology    : 138
% 3.16/1.61  #SimpNegUnit  : 6
% 3.16/1.61  #BackRed      : 0
% 3.16/1.61  
% 3.16/1.61  #Partial instantiations: 0
% 3.16/1.61  #Strategies tried      : 1
% 3.16/1.61  
% 3.16/1.61  Timing (in seconds)
% 3.16/1.61  ----------------------
% 3.16/1.61  Preprocessing        : 0.34
% 3.16/1.61  Parsing              : 0.18
% 3.16/1.61  CNF conversion       : 0.03
% 3.16/1.61  Main loop            : 0.44
% 3.16/1.61  Inferencing          : 0.18
% 3.16/1.61  Reduction            : 0.12
% 3.16/1.62  Demodulation         : 0.08
% 3.16/1.62  BG Simplification    : 0.02
% 3.16/1.62  Subsumption          : 0.08
% 3.16/1.62  Abstraction          : 0.02
% 3.16/1.62  MUC search           : 0.00
% 3.16/1.62  Cooper               : 0.00
% 3.16/1.62  Total                : 0.82
% 3.16/1.62  Index Insertion      : 0.00
% 3.16/1.62  Index Deletion       : 0.00
% 3.16/1.62  Index Matching       : 0.00
% 3.16/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
