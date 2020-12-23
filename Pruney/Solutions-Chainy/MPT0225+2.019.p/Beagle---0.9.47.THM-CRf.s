%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:33 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 165 expanded)
%              Number of leaves         :   29 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  139 ( 330 expanded)
%              Number of equality atoms :   38 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [C_26,A_22] :
      ( r2_hidden(C_26,k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_981,plain,(
    ! [A_210,B_211,C_212] :
      ( ~ r1_xboole_0(A_210,B_211)
      | ~ r2_hidden(C_212,B_211)
      | ~ r2_hidden(C_212,A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1025,plain,(
    ! [C_221,B_222,A_223] :
      ( ~ r2_hidden(C_221,B_222)
      | ~ r2_hidden(C_221,k1_tarski(A_223))
      | r2_hidden(A_223,B_222) ) ),
    inference(resolution,[status(thm)],[c_42,c_981])).

tff(c_1073,plain,(
    ! [A_237,B_238,A_239] :
      ( ~ r2_hidden('#skF_1'(A_237,B_238),k1_tarski(A_239))
      | r2_hidden(A_239,A_237)
      | r1_xboole_0(A_237,B_238) ) ),
    inference(resolution,[status(thm)],[c_6,c_1025])).

tff(c_1116,plain,(
    ! [A_244,B_245] :
      ( r2_hidden(A_244,k1_tarski(A_244))
      | r1_xboole_0(k1_tarski(A_244),B_245) ) ),
    inference(resolution,[status(thm)],[c_6,c_1073])).

tff(c_46,plain,
    ( '#skF_5' != '#skF_4'
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_53,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_78,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(k1_tarski(A_39),B_40)
      | r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_145,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(k1_tarski(A_63),B_64) = k1_tarski(A_63)
      | r2_hidden(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_78,c_16])).

tff(c_44,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_84,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_160,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_84])).

tff(c_82,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(k1_tarski(A_39),B_40) = k1_tarski(A_39)
      | r2_hidden(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_78,c_16])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,B_56)
      | ~ r2_hidden(C_57,A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_204,plain,(
    ! [C_78,B_79,A_80] :
      ( ~ r2_hidden(C_78,B_79)
      | ~ r2_hidden(C_78,A_80)
      | k4_xboole_0(A_80,B_79) != A_80 ) ),
    inference(resolution,[status(thm)],[c_18,c_128])).

tff(c_344,plain,(
    ! [A_102,B_103,A_104] :
      ( ~ r2_hidden('#skF_1'(A_102,B_103),A_104)
      | k4_xboole_0(A_104,A_102) != A_104
      | r1_xboole_0(A_102,B_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_204])).

tff(c_358,plain,(
    ! [B_105,A_106] :
      ( k4_xboole_0(B_105,A_106) != B_105
      | r1_xboole_0(A_106,B_105) ) ),
    inference(resolution,[status(thm)],[c_4,c_344])).

tff(c_40,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden(A_27,B_28)
      | ~ r1_xboole_0(k1_tarski(A_27),B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_377,plain,(
    ! [A_111,B_112] :
      ( ~ r2_hidden(A_111,B_112)
      | k4_xboole_0(B_112,k1_tarski(A_111)) != B_112 ) ),
    inference(resolution,[status(thm)],[c_358,c_40])).

tff(c_557,plain,(
    ! [A_124,A_125] :
      ( ~ r2_hidden(A_124,k1_tarski(A_125))
      | r2_hidden(A_125,k1_tarski(A_124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_377])).

tff(c_578,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_160,c_557])).

tff(c_162,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,k1_tarski(A_67))
      | r2_hidden(A_67,B_66) ) ),
    inference(resolution,[status(thm)],[c_42,c_128])).

tff(c_174,plain,(
    ! [C_26,A_67,A_22] :
      ( ~ r2_hidden(C_26,k1_tarski(A_67))
      | r2_hidden(A_67,k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(resolution,[status(thm)],[c_30,c_162])).

tff(c_600,plain,(
    ! [A_126] :
      ( r2_hidden('#skF_4',k1_zfmisc_1(A_126))
      | ~ r1_tarski('#skF_5',A_126) ) ),
    inference(resolution,[status(thm)],[c_578,c_174])).

tff(c_28,plain,(
    ! [C_26,A_22] :
      ( r1_tarski(C_26,A_22)
      | ~ r2_hidden(C_26,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_614,plain,(
    ! [A_127] :
      ( r1_tarski('#skF_4',A_127)
      | ~ r1_tarski('#skF_5',A_127) ) ),
    inference(resolution,[status(thm)],[c_600,c_28])).

tff(c_623,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_614])).

tff(c_232,plain,(
    ! [C_83,A_84,A_85] :
      ( ~ r2_hidden(C_83,k1_tarski(A_84))
      | r2_hidden(A_84,k1_zfmisc_1(A_85))
      | ~ r1_tarski(C_83,A_85) ) ),
    inference(resolution,[status(thm)],[c_30,c_162])).

tff(c_263,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_5',k1_zfmisc_1(A_88))
      | ~ r1_tarski('#skF_4',A_88) ) ),
    inference(resolution,[status(thm)],[c_160,c_232])).

tff(c_274,plain,(
    ! [A_89] :
      ( r1_tarski('#skF_5',A_89)
      | ~ r1_tarski('#skF_4',A_89) ) ),
    inference(resolution,[status(thm)],[c_263,c_28])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_277,plain,(
    ! [A_89] :
      ( A_89 = '#skF_5'
      | ~ r1_tarski(A_89,'#skF_5')
      | ~ r1_tarski('#skF_4',A_89) ) ),
    inference(resolution,[status(thm)],[c_274,c_8])).

tff(c_625,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_623,c_277])).

tff(c_630,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_625])).

tff(c_632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_630])).

tff(c_633,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_634,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_743,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_634,c_48])).

tff(c_696,plain,(
    ! [A_143,B_144,C_145] :
      ( ~ r1_xboole_0(A_143,B_144)
      | ~ r2_hidden(C_145,B_144)
      | ~ r2_hidden(C_145,A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_774,plain,(
    ! [C_161,B_162,A_163] :
      ( ~ r2_hidden(C_161,B_162)
      | ~ r2_hidden(C_161,A_163)
      | k4_xboole_0(A_163,B_162) != A_163 ) ),
    inference(resolution,[status(thm)],[c_18,c_696])).

tff(c_822,plain,(
    ! [A_172,B_173,A_174] :
      ( ~ r2_hidden('#skF_1'(A_172,B_173),A_174)
      | k4_xboole_0(A_174,A_172) != A_174
      | r1_xboole_0(A_172,B_173) ) ),
    inference(resolution,[status(thm)],[c_6,c_774])).

tff(c_850,plain,(
    ! [A_179,B_180] :
      ( k4_xboole_0(A_179,A_179) != A_179
      | r1_xboole_0(A_179,B_180) ) ),
    inference(resolution,[status(thm)],[c_6,c_822])).

tff(c_858,plain,(
    ! [B_181] : r1_xboole_0(k1_tarski('#skF_6'),B_181) ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_850])).

tff(c_870,plain,(
    ! [B_182] : ~ r2_hidden('#skF_6',B_182) ),
    inference(resolution,[status(thm)],[c_858,c_40])).

tff(c_876,plain,(
    ! [A_183] : ~ r1_tarski('#skF_6',A_183) ),
    inference(resolution,[status(thm)],[c_30,c_870])).

tff(c_881,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_876])).

tff(c_882,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_883,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( '#skF_5' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_912,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_882,c_883,c_50])).

tff(c_918,plain,(
    ! [A_191,B_192] :
      ( r1_xboole_0(A_191,B_192)
      | k4_xboole_0(A_191,B_192) != A_191 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_988,plain,(
    ! [A_213,B_214] :
      ( ~ r2_hidden(A_213,B_214)
      | k4_xboole_0(k1_tarski(A_213),B_214) != k1_tarski(A_213) ) ),
    inference(resolution,[status(thm)],[c_918,c_40])).

tff(c_992,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_988])).

tff(c_1149,plain,(
    ! [B_246] : r1_xboole_0(k1_tarski('#skF_6'),B_246) ),
    inference(resolution,[status(thm)],[c_1116,c_992])).

tff(c_1161,plain,(
    ! [B_247] : ~ r2_hidden('#skF_6',B_247) ),
    inference(resolution,[status(thm)],[c_1149,c_40])).

tff(c_1196,plain,(
    ! [A_249] : ~ r1_tarski('#skF_6',A_249) ),
    inference(resolution,[status(thm)],[c_30,c_1161])).

tff(c_1201,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_1196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.59  
% 3.04/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.04/1.59  
% 3.04/1.59  %Foreground sorts:
% 3.04/1.59  
% 3.04/1.59  
% 3.04/1.59  %Background operators:
% 3.04/1.59  
% 3.04/1.59  
% 3.04/1.59  %Foreground operators:
% 3.04/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.04/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.04/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.04/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.04/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.04/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.04/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.04/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.04/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.59  
% 3.04/1.60  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.04/1.60  tff(f_70, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.04/1.60  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.04/1.60  tff(f_80, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.04/1.60  tff(f_86, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.04/1.60  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.04/1.60  tff(f_75, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.04/1.60  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.04/1.60  tff(c_30, plain, (![C_26, A_22]: (r2_hidden(C_26, k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.04/1.60  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.60  tff(c_42, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.04/1.60  tff(c_981, plain, (![A_210, B_211, C_212]: (~r1_xboole_0(A_210, B_211) | ~r2_hidden(C_212, B_211) | ~r2_hidden(C_212, A_210))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.60  tff(c_1025, plain, (![C_221, B_222, A_223]: (~r2_hidden(C_221, B_222) | ~r2_hidden(C_221, k1_tarski(A_223)) | r2_hidden(A_223, B_222))), inference(resolution, [status(thm)], [c_42, c_981])).
% 3.04/1.60  tff(c_1073, plain, (![A_237, B_238, A_239]: (~r2_hidden('#skF_1'(A_237, B_238), k1_tarski(A_239)) | r2_hidden(A_239, A_237) | r1_xboole_0(A_237, B_238))), inference(resolution, [status(thm)], [c_6, c_1025])).
% 3.04/1.60  tff(c_1116, plain, (![A_244, B_245]: (r2_hidden(A_244, k1_tarski(A_244)) | r1_xboole_0(k1_tarski(A_244), B_245))), inference(resolution, [status(thm)], [c_6, c_1073])).
% 3.04/1.60  tff(c_46, plain, ('#skF_5'!='#skF_4' | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.04/1.60  tff(c_53, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_46])).
% 3.04/1.60  tff(c_78, plain, (![A_39, B_40]: (r1_xboole_0(k1_tarski(A_39), B_40) | r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.04/1.60  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.60  tff(c_145, plain, (![A_63, B_64]: (k4_xboole_0(k1_tarski(A_63), B_64)=k1_tarski(A_63) | r2_hidden(A_63, B_64))), inference(resolution, [status(thm)], [c_78, c_16])).
% 3.04/1.60  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | '#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.04/1.60  tff(c_84, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 3.04/1.60  tff(c_160, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_84])).
% 3.04/1.60  tff(c_82, plain, (![A_39, B_40]: (k4_xboole_0(k1_tarski(A_39), B_40)=k1_tarski(A_39) | r2_hidden(A_39, B_40))), inference(resolution, [status(thm)], [c_78, c_16])).
% 3.04/1.60  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.60  tff(c_18, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.60  tff(c_128, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, B_56) | ~r2_hidden(C_57, A_55))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.60  tff(c_204, plain, (![C_78, B_79, A_80]: (~r2_hidden(C_78, B_79) | ~r2_hidden(C_78, A_80) | k4_xboole_0(A_80, B_79)!=A_80)), inference(resolution, [status(thm)], [c_18, c_128])).
% 3.04/1.60  tff(c_344, plain, (![A_102, B_103, A_104]: (~r2_hidden('#skF_1'(A_102, B_103), A_104) | k4_xboole_0(A_104, A_102)!=A_104 | r1_xboole_0(A_102, B_103))), inference(resolution, [status(thm)], [c_6, c_204])).
% 3.04/1.60  tff(c_358, plain, (![B_105, A_106]: (k4_xboole_0(B_105, A_106)!=B_105 | r1_xboole_0(A_106, B_105))), inference(resolution, [status(thm)], [c_4, c_344])).
% 3.04/1.60  tff(c_40, plain, (![A_27, B_28]: (~r2_hidden(A_27, B_28) | ~r1_xboole_0(k1_tarski(A_27), B_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.04/1.60  tff(c_377, plain, (![A_111, B_112]: (~r2_hidden(A_111, B_112) | k4_xboole_0(B_112, k1_tarski(A_111))!=B_112)), inference(resolution, [status(thm)], [c_358, c_40])).
% 3.04/1.60  tff(c_557, plain, (![A_124, A_125]: (~r2_hidden(A_124, k1_tarski(A_125)) | r2_hidden(A_125, k1_tarski(A_124)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_377])).
% 3.04/1.60  tff(c_578, plain, (r2_hidden('#skF_5', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_160, c_557])).
% 3.04/1.60  tff(c_162, plain, (![C_65, B_66, A_67]: (~r2_hidden(C_65, B_66) | ~r2_hidden(C_65, k1_tarski(A_67)) | r2_hidden(A_67, B_66))), inference(resolution, [status(thm)], [c_42, c_128])).
% 3.04/1.60  tff(c_174, plain, (![C_26, A_67, A_22]: (~r2_hidden(C_26, k1_tarski(A_67)) | r2_hidden(A_67, k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(resolution, [status(thm)], [c_30, c_162])).
% 3.04/1.60  tff(c_600, plain, (![A_126]: (r2_hidden('#skF_4', k1_zfmisc_1(A_126)) | ~r1_tarski('#skF_5', A_126))), inference(resolution, [status(thm)], [c_578, c_174])).
% 3.04/1.60  tff(c_28, plain, (![C_26, A_22]: (r1_tarski(C_26, A_22) | ~r2_hidden(C_26, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.04/1.60  tff(c_614, plain, (![A_127]: (r1_tarski('#skF_4', A_127) | ~r1_tarski('#skF_5', A_127))), inference(resolution, [status(thm)], [c_600, c_28])).
% 3.04/1.60  tff(c_623, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_12, c_614])).
% 3.04/1.60  tff(c_232, plain, (![C_83, A_84, A_85]: (~r2_hidden(C_83, k1_tarski(A_84)) | r2_hidden(A_84, k1_zfmisc_1(A_85)) | ~r1_tarski(C_83, A_85))), inference(resolution, [status(thm)], [c_30, c_162])).
% 3.04/1.60  tff(c_263, plain, (![A_88]: (r2_hidden('#skF_5', k1_zfmisc_1(A_88)) | ~r1_tarski('#skF_4', A_88))), inference(resolution, [status(thm)], [c_160, c_232])).
% 3.04/1.60  tff(c_274, plain, (![A_89]: (r1_tarski('#skF_5', A_89) | ~r1_tarski('#skF_4', A_89))), inference(resolution, [status(thm)], [c_263, c_28])).
% 3.04/1.60  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.04/1.60  tff(c_277, plain, (![A_89]: (A_89='#skF_5' | ~r1_tarski(A_89, '#skF_5') | ~r1_tarski('#skF_4', A_89))), inference(resolution, [status(thm)], [c_274, c_8])).
% 3.04/1.60  tff(c_625, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_623, c_277])).
% 3.04/1.60  tff(c_630, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_625])).
% 3.04/1.60  tff(c_632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_630])).
% 3.04/1.60  tff(c_633, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 3.04/1.60  tff(c_634, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 3.04/1.60  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.04/1.60  tff(c_743, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_633, c_634, c_48])).
% 3.04/1.60  tff(c_696, plain, (![A_143, B_144, C_145]: (~r1_xboole_0(A_143, B_144) | ~r2_hidden(C_145, B_144) | ~r2_hidden(C_145, A_143))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.60  tff(c_774, plain, (![C_161, B_162, A_163]: (~r2_hidden(C_161, B_162) | ~r2_hidden(C_161, A_163) | k4_xboole_0(A_163, B_162)!=A_163)), inference(resolution, [status(thm)], [c_18, c_696])).
% 3.04/1.60  tff(c_822, plain, (![A_172, B_173, A_174]: (~r2_hidden('#skF_1'(A_172, B_173), A_174) | k4_xboole_0(A_174, A_172)!=A_174 | r1_xboole_0(A_172, B_173))), inference(resolution, [status(thm)], [c_6, c_774])).
% 3.04/1.60  tff(c_850, plain, (![A_179, B_180]: (k4_xboole_0(A_179, A_179)!=A_179 | r1_xboole_0(A_179, B_180))), inference(resolution, [status(thm)], [c_6, c_822])).
% 3.04/1.60  tff(c_858, plain, (![B_181]: (r1_xboole_0(k1_tarski('#skF_6'), B_181))), inference(superposition, [status(thm), theory('equality')], [c_743, c_850])).
% 3.04/1.60  tff(c_870, plain, (![B_182]: (~r2_hidden('#skF_6', B_182))), inference(resolution, [status(thm)], [c_858, c_40])).
% 3.04/1.60  tff(c_876, plain, (![A_183]: (~r1_tarski('#skF_6', A_183))), inference(resolution, [status(thm)], [c_30, c_870])).
% 3.04/1.60  tff(c_881, plain, $false, inference(resolution, [status(thm)], [c_12, c_876])).
% 3.04/1.60  tff(c_882, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 3.04/1.60  tff(c_883, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 3.04/1.60  tff(c_50, plain, ('#skF_5'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.04/1.60  tff(c_912, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_882, c_883, c_50])).
% 3.04/1.60  tff(c_918, plain, (![A_191, B_192]: (r1_xboole_0(A_191, B_192) | k4_xboole_0(A_191, B_192)!=A_191)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.60  tff(c_988, plain, (![A_213, B_214]: (~r2_hidden(A_213, B_214) | k4_xboole_0(k1_tarski(A_213), B_214)!=k1_tarski(A_213))), inference(resolution, [status(thm)], [c_918, c_40])).
% 3.04/1.60  tff(c_992, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_912, c_988])).
% 3.04/1.60  tff(c_1149, plain, (![B_246]: (r1_xboole_0(k1_tarski('#skF_6'), B_246))), inference(resolution, [status(thm)], [c_1116, c_992])).
% 3.04/1.60  tff(c_1161, plain, (![B_247]: (~r2_hidden('#skF_6', B_247))), inference(resolution, [status(thm)], [c_1149, c_40])).
% 3.04/1.60  tff(c_1196, plain, (![A_249]: (~r1_tarski('#skF_6', A_249))), inference(resolution, [status(thm)], [c_30, c_1161])).
% 3.04/1.60  tff(c_1201, plain, $false, inference(resolution, [status(thm)], [c_12, c_1196])).
% 3.04/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.60  
% 3.04/1.60  Inference rules
% 3.04/1.60  ----------------------
% 3.04/1.60  #Ref     : 0
% 3.04/1.60  #Sup     : 277
% 3.04/1.60  #Fact    : 0
% 3.04/1.60  #Define  : 0
% 3.04/1.60  #Split   : 2
% 3.04/1.60  #Chain   : 0
% 3.04/1.60  #Close   : 0
% 3.04/1.60  
% 3.04/1.60  Ordering : KBO
% 3.04/1.60  
% 3.04/1.60  Simplification rules
% 3.04/1.60  ----------------------
% 3.04/1.60  #Subsume      : 27
% 3.04/1.60  #Demod        : 34
% 3.04/1.60  #Tautology    : 93
% 3.04/1.60  #SimpNegUnit  : 5
% 3.04/1.60  #BackRed      : 0
% 3.04/1.60  
% 3.04/1.60  #Partial instantiations: 0
% 3.04/1.60  #Strategies tried      : 1
% 3.04/1.60  
% 3.04/1.60  Timing (in seconds)
% 3.04/1.60  ----------------------
% 3.04/1.61  Preprocessing        : 0.36
% 3.04/1.61  Parsing              : 0.17
% 3.04/1.61  CNF conversion       : 0.03
% 3.04/1.61  Main loop            : 0.40
% 3.04/1.61  Inferencing          : 0.15
% 3.04/1.61  Reduction            : 0.10
% 3.04/1.61  Demodulation         : 0.07
% 3.04/1.61  BG Simplification    : 0.02
% 3.04/1.61  Subsumption          : 0.08
% 3.04/1.61  Abstraction          : 0.02
% 3.04/1.61  MUC search           : 0.00
% 3.04/1.61  Cooper               : 0.00
% 3.04/1.61  Total                : 0.80
% 3.04/1.61  Index Insertion      : 0.00
% 3.04/1.61  Index Deletion       : 0.00
% 3.04/1.61  Index Matching       : 0.00
% 3.04/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
