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
% DateTime   : Thu Dec  3 09:53:44 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 561 expanded)
%              Number of leaves         :   25 ( 170 expanded)
%              Depth                    :   10
%              Number of atoms          :  185 (1247 expanded)
%              Number of equality atoms :   77 ( 959 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2013,plain,(
    ! [A_415,B_416,D_417] :
      ( r2_hidden('#skF_6'(A_415,B_416,k2_zfmisc_1(A_415,B_416),D_417),A_415)
      | ~ r2_hidden(D_417,k2_zfmisc_1(A_415,B_416)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1696,plain,(
    ! [A_358,B_359,D_360] :
      ( r2_hidden('#skF_7'(A_358,B_359,k2_zfmisc_1(A_358,B_359),D_360),B_359)
      | ~ r2_hidden(D_360,k2_zfmisc_1(A_358,B_359)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1396,plain,(
    ! [A_303,B_304,D_305] :
      ( r2_hidden('#skF_6'(A_303,B_304,k2_zfmisc_1(A_303,B_304),D_305),A_303)
      | ~ r2_hidden(D_305,k2_zfmisc_1(A_303,B_304)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1048,plain,(
    ! [A_243,B_244,D_245] :
      ( r2_hidden('#skF_7'(A_243,B_244,k2_zfmisc_1(A_243,B_244),D_245),B_244)
      | ~ r2_hidden(D_245,k2_zfmisc_1(A_243,B_244)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_690,plain,(
    ! [A_178,B_179,D_180] :
      ( r2_hidden('#skF_6'(A_178,B_179,k2_zfmisc_1(A_178,B_179),D_180),A_178)
      | ~ r2_hidden(D_180,k2_zfmisc_1(A_178,B_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_465,plain,(
    ! [A_130,B_131,D_132] :
      ( r2_hidden('#skF_7'(A_130,B_131,k2_zfmisc_1(A_130,B_131),D_132),B_131)
      | ~ r2_hidden(D_132,k2_zfmisc_1(A_130,B_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_73,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_10,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_105,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,B_60)
      | ~ r2_hidden(C_61,A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [C_61] : ~ r2_hidden(C_61,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_105])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_74,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_193,plain,(
    ! [A_77,B_78,C_79,D_80] :
      ( r2_hidden(k4_tarski(A_77,B_78),k2_zfmisc_1(C_79,D_80))
      | ~ r2_hidden(B_78,D_80)
      | ~ r2_hidden(A_77,C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_204,plain,(
    ! [A_77,B_78] :
      ( r2_hidden(k4_tarski(A_77,B_78),k1_xboole_0)
      | ~ r2_hidden(B_78,'#skF_11')
      | ~ r2_hidden(A_77,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_193])).

tff(c_208,plain,(
    ! [B_78,A_77] :
      ( ~ r2_hidden(B_78,'#skF_11')
      | ~ r2_hidden(A_77,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_204])).

tff(c_210,plain,(
    ! [A_81] : ~ r2_hidden(A_81,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_221,plain,(
    ! [B_82] : r1_xboole_0('#skF_10',B_82) ),
    inference(resolution,[status(thm)],[c_6,c_210])).

tff(c_12,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_230,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_221,c_12])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_230])).

tff(c_238,plain,(
    ! [B_83] : ~ r2_hidden(B_83,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_249,plain,(
    ! [B_84] : r1_xboole_0('#skF_11',B_84) ),
    inference(resolution,[status(thm)],[c_6,c_238])).

tff(c_258,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_249,c_12])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_258])).

tff(c_265,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_267,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_272,plain,(
    r1_xboole_0('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_267,c_10])).

tff(c_318,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_xboole_0(A_96,B_97)
      | ~ r2_hidden(C_98,B_97)
      | ~ r2_hidden(C_98,A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_324,plain,(
    ! [C_98] : ~ r2_hidden(C_98,'#skF_9') ),
    inference(resolution,[status(thm)],[c_272,c_318])).

tff(c_474,plain,(
    ! [D_133,A_134] : ~ r2_hidden(D_133,k2_zfmisc_1(A_134,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_465,c_324])).

tff(c_495,plain,(
    ! [A_135,A_136] : r1_xboole_0(A_135,k2_zfmisc_1(A_136,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_4,c_474])).

tff(c_270,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | A_7 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_12])).

tff(c_507,plain,(
    ! [A_136] : k2_zfmisc_1(A_136,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_495,c_270])).

tff(c_266,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_284,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_266])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_291,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_267,c_56])).

tff(c_292,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_291])).

tff(c_513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_292])).

tff(c_514,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_520,plain,(
    r1_xboole_0('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_514,c_10])).

tff(c_567,plain,(
    ! [A_148,B_149,C_150] :
      ( ~ r1_xboole_0(A_148,B_149)
      | ~ r2_hidden(C_150,B_149)
      | ~ r2_hidden(C_150,A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_573,plain,(
    ! [C_150] : ~ r2_hidden(C_150,'#skF_8') ),
    inference(resolution,[status(thm)],[c_520,c_567])).

tff(c_699,plain,(
    ! [D_181,B_182] : ~ r2_hidden(D_181,k2_zfmisc_1('#skF_8',B_182)) ),
    inference(resolution,[status(thm)],[c_690,c_573])).

tff(c_720,plain,(
    ! [A_183,B_184] : r1_xboole_0(A_183,k2_zfmisc_1('#skF_8',B_184)) ),
    inference(resolution,[status(thm)],[c_4,c_699])).

tff(c_518,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | A_7 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_12])).

tff(c_732,plain,(
    ! [B_184] : k2_zfmisc_1('#skF_8',B_184) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_720,c_518])).

tff(c_526,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_266])).

tff(c_527,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_514,c_56])).

tff(c_528,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_527])).

tff(c_738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_528])).

tff(c_740,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_739,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_749,plain,
    ( '#skF_11' = '#skF_8'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_740,c_739])).

tff(c_750,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_749])).

tff(c_744,plain,(
    r1_xboole_0('#skF_11','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_740,c_10])).

tff(c_751,plain,(
    r1_xboole_0('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_750,c_744])).

tff(c_808,plain,(
    ! [A_196,B_197,C_198] :
      ( ~ r1_xboole_0(A_196,B_197)
      | ~ r2_hidden(C_198,B_197)
      | ~ r2_hidden(C_198,A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_814,plain,(
    ! [C_198] : ~ r2_hidden(C_198,'#skF_9') ),
    inference(resolution,[status(thm)],[c_751,c_808])).

tff(c_1064,plain,(
    ! [D_246,A_247] : ~ r2_hidden(D_246,k2_zfmisc_1(A_247,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_1048,c_814])).

tff(c_1093,plain,(
    ! [A_248,A_249] : r1_xboole_0(A_248,k2_zfmisc_1(A_249,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_4,c_1064])).

tff(c_742,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | A_7 = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_12])).

tff(c_772,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | A_7 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_742])).

tff(c_1108,plain,(
    ! [A_249] : k2_zfmisc_1(A_249,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1093,c_772])).

tff(c_753,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_740])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_780,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_750,c_753,c_48])).

tff(c_1115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_780])).

tff(c_1116,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_749])).

tff(c_1119,plain,(
    r1_xboole_0('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_1116,c_744])).

tff(c_1176,plain,(
    ! [A_261,B_262,C_263] :
      ( ~ r1_xboole_0(A_261,B_262)
      | ~ r2_hidden(C_263,B_262)
      | ~ r2_hidden(C_263,A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1182,plain,(
    ! [C_263] : ~ r2_hidden(C_263,'#skF_8') ),
    inference(resolution,[status(thm)],[c_1119,c_1176])).

tff(c_1412,plain,(
    ! [D_306,B_307] : ~ r2_hidden(D_306,k2_zfmisc_1('#skF_8',B_307)) ),
    inference(resolution,[status(thm)],[c_1396,c_1182])).

tff(c_1441,plain,(
    ! [B_308,B_309] : r1_xboole_0(k2_zfmisc_1('#skF_8',B_308),B_309) ),
    inference(resolution,[status(thm)],[c_6,c_1412])).

tff(c_1139,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | A_7 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_742])).

tff(c_1456,plain,(
    ! [B_308] : k2_zfmisc_1('#skF_8',B_308) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1441,c_1139])).

tff(c_1121,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_740])).

tff(c_1147,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1116,c_1121,c_48])).

tff(c_1463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_1147])).

tff(c_1465,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1464,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1482,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_1465,c_1464])).

tff(c_1483,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1482])).

tff(c_1469,plain,(
    r1_xboole_0('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_1465,c_10])).

tff(c_1485,plain,(
    r1_xboole_0('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1483,c_1483,c_1469])).

tff(c_1540,plain,(
    ! [A_322,B_323,C_324] :
      ( ~ r1_xboole_0(A_322,B_323)
      | ~ r2_hidden(C_324,B_323)
      | ~ r2_hidden(C_324,A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1546,plain,(
    ! [C_324] : ~ r2_hidden(C_324,'#skF_9') ),
    inference(resolution,[status(thm)],[c_1485,c_1540])).

tff(c_1705,plain,(
    ! [D_361,A_362] : ~ r2_hidden(D_361,k2_zfmisc_1(A_362,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_1696,c_1546])).

tff(c_1726,plain,(
    ! [A_363,A_364] : r1_xboole_0(A_363,k2_zfmisc_1(A_364,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_4,c_1705])).

tff(c_1467,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | A_7 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_12])).

tff(c_1505,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | A_7 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1483,c_1467])).

tff(c_1738,plain,(
    ! [A_364] : k2_zfmisc_1(A_364,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1726,c_1505])).

tff(c_1487,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1483,c_1465])).

tff(c_52,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1497,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_1483,c_1487,c_52])).

tff(c_1744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1738,c_1497])).

tff(c_1745,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1482])).

tff(c_1751,plain,(
    r1_xboole_0('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1745,c_1745,c_1469])).

tff(c_1806,plain,(
    ! [A_376,B_377,C_378] :
      ( ~ r1_xboole_0(A_376,B_377)
      | ~ r2_hidden(C_378,B_377)
      | ~ r2_hidden(C_378,A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1812,plain,(
    ! [C_378] : ~ r2_hidden(C_378,'#skF_8') ),
    inference(resolution,[status(thm)],[c_1751,c_1806])).

tff(c_2026,plain,(
    ! [D_418,B_419] : ~ r2_hidden(D_418,k2_zfmisc_1('#skF_8',B_419)) ),
    inference(resolution,[status(thm)],[c_2013,c_1812])).

tff(c_2055,plain,(
    ! [B_420,B_421] : r1_xboole_0(k2_zfmisc_1('#skF_8',B_420),B_421) ),
    inference(resolution,[status(thm)],[c_6,c_2026])).

tff(c_1770,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | A_7 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1745,c_1467])).

tff(c_2070,plain,(
    ! [B_420] : k2_zfmisc_1('#skF_8',B_420) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2055,c_1770])).

tff(c_1748,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_1465,c_52])).

tff(c_1749,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1745,c_1748])).

tff(c_2077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2070,c_1749])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.50  
% 3.25/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.51  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 3.25/1.51  
% 3.25/1.51  %Foreground sorts:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Background operators:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Foreground operators:
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.51  tff('#skF_11', type, '#skF_11': $i).
% 3.25/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.25/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.25/1.51  tff('#skF_10', type, '#skF_10': $i).
% 3.25/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.25/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.25/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.25/1.51  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.25/1.51  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.25/1.51  tff('#skF_9', type, '#skF_9': $i).
% 3.25/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.25/1.51  
% 3.25/1.53  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.25/1.53  tff(f_73, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.25/1.53  tff(f_86, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.25/1.53  tff(f_57, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.25/1.53  tff(f_79, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.25/1.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.53  tff(c_2013, plain, (![A_415, B_416, D_417]: (r2_hidden('#skF_6'(A_415, B_416, k2_zfmisc_1(A_415, B_416), D_417), A_415) | ~r2_hidden(D_417, k2_zfmisc_1(A_415, B_416)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.25/1.53  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.53  tff(c_1696, plain, (![A_358, B_359, D_360]: (r2_hidden('#skF_7'(A_358, B_359, k2_zfmisc_1(A_358, B_359), D_360), B_359) | ~r2_hidden(D_360, k2_zfmisc_1(A_358, B_359)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.25/1.53  tff(c_1396, plain, (![A_303, B_304, D_305]: (r2_hidden('#skF_6'(A_303, B_304, k2_zfmisc_1(A_303, B_304), D_305), A_303) | ~r2_hidden(D_305, k2_zfmisc_1(A_303, B_304)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.25/1.53  tff(c_1048, plain, (![A_243, B_244, D_245]: (r2_hidden('#skF_7'(A_243, B_244, k2_zfmisc_1(A_243, B_244), D_245), B_244) | ~r2_hidden(D_245, k2_zfmisc_1(A_243, B_244)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.25/1.53  tff(c_690, plain, (![A_178, B_179, D_180]: (r2_hidden('#skF_6'(A_178, B_179, k2_zfmisc_1(A_178, B_179), D_180), A_178) | ~r2_hidden(D_180, k2_zfmisc_1(A_178, B_179)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.25/1.53  tff(c_465, plain, (![A_130, B_131, D_132]: (r2_hidden('#skF_7'(A_130, B_131, k2_zfmisc_1(A_130, B_131), D_132), B_131) | ~r2_hidden(D_132, k2_zfmisc_1(A_130, B_131)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.25/1.53  tff(c_50, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.25/1.53  tff(c_73, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_50])).
% 3.25/1.53  tff(c_54, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.25/1.53  tff(c_72, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_54])).
% 3.25/1.53  tff(c_10, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.53  tff(c_105, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, B_60) | ~r2_hidden(C_61, A_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.53  tff(c_111, plain, (![C_61]: (~r2_hidden(C_61, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_105])).
% 3.25/1.53  tff(c_58, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.25/1.53  tff(c_74, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 3.25/1.53  tff(c_193, plain, (![A_77, B_78, C_79, D_80]: (r2_hidden(k4_tarski(A_77, B_78), k2_zfmisc_1(C_79, D_80)) | ~r2_hidden(B_78, D_80) | ~r2_hidden(A_77, C_79))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.25/1.53  tff(c_204, plain, (![A_77, B_78]: (r2_hidden(k4_tarski(A_77, B_78), k1_xboole_0) | ~r2_hidden(B_78, '#skF_11') | ~r2_hidden(A_77, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_193])).
% 3.25/1.53  tff(c_208, plain, (![B_78, A_77]: (~r2_hidden(B_78, '#skF_11') | ~r2_hidden(A_77, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_111, c_204])).
% 3.25/1.53  tff(c_210, plain, (![A_81]: (~r2_hidden(A_81, '#skF_10'))), inference(splitLeft, [status(thm)], [c_208])).
% 3.25/1.53  tff(c_221, plain, (![B_82]: (r1_xboole_0('#skF_10', B_82))), inference(resolution, [status(thm)], [c_6, c_210])).
% 3.25/1.53  tff(c_12, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.53  tff(c_230, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_221, c_12])).
% 3.25/1.53  tff(c_236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_230])).
% 3.25/1.53  tff(c_238, plain, (![B_83]: (~r2_hidden(B_83, '#skF_11'))), inference(splitRight, [status(thm)], [c_208])).
% 3.25/1.53  tff(c_249, plain, (![B_84]: (r1_xboole_0('#skF_11', B_84))), inference(resolution, [status(thm)], [c_6, c_238])).
% 3.25/1.53  tff(c_258, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_249, c_12])).
% 3.25/1.53  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_258])).
% 3.25/1.53  tff(c_265, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_58])).
% 3.25/1.53  tff(c_267, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_265])).
% 3.25/1.53  tff(c_272, plain, (r1_xboole_0('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_267, c_267, c_10])).
% 3.25/1.53  tff(c_318, plain, (![A_96, B_97, C_98]: (~r1_xboole_0(A_96, B_97) | ~r2_hidden(C_98, B_97) | ~r2_hidden(C_98, A_96))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.53  tff(c_324, plain, (![C_98]: (~r2_hidden(C_98, '#skF_9'))), inference(resolution, [status(thm)], [c_272, c_318])).
% 3.25/1.53  tff(c_474, plain, (![D_133, A_134]: (~r2_hidden(D_133, k2_zfmisc_1(A_134, '#skF_9')))), inference(resolution, [status(thm)], [c_465, c_324])).
% 3.25/1.53  tff(c_495, plain, (![A_135, A_136]: (r1_xboole_0(A_135, k2_zfmisc_1(A_136, '#skF_9')))), inference(resolution, [status(thm)], [c_4, c_474])).
% 3.25/1.53  tff(c_270, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | A_7='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_267, c_12])).
% 3.25/1.53  tff(c_507, plain, (![A_136]: (k2_zfmisc_1(A_136, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_495, c_270])).
% 3.25/1.53  tff(c_266, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 3.25/1.53  tff(c_284, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_267, c_266])).
% 3.25/1.53  tff(c_56, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.25/1.53  tff(c_291, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_267, c_267, c_56])).
% 3.25/1.53  tff(c_292, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_284, c_291])).
% 3.25/1.53  tff(c_513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_507, c_292])).
% 3.25/1.53  tff(c_514, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_265])).
% 3.25/1.53  tff(c_520, plain, (r1_xboole_0('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_514, c_10])).
% 3.25/1.53  tff(c_567, plain, (![A_148, B_149, C_150]: (~r1_xboole_0(A_148, B_149) | ~r2_hidden(C_150, B_149) | ~r2_hidden(C_150, A_148))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.53  tff(c_573, plain, (![C_150]: (~r2_hidden(C_150, '#skF_8'))), inference(resolution, [status(thm)], [c_520, c_567])).
% 3.25/1.53  tff(c_699, plain, (![D_181, B_182]: (~r2_hidden(D_181, k2_zfmisc_1('#skF_8', B_182)))), inference(resolution, [status(thm)], [c_690, c_573])).
% 3.25/1.53  tff(c_720, plain, (![A_183, B_184]: (r1_xboole_0(A_183, k2_zfmisc_1('#skF_8', B_184)))), inference(resolution, [status(thm)], [c_4, c_699])).
% 3.25/1.53  tff(c_518, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | A_7='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_12])).
% 3.25/1.53  tff(c_732, plain, (![B_184]: (k2_zfmisc_1('#skF_8', B_184)='#skF_8')), inference(resolution, [status(thm)], [c_720, c_518])).
% 3.25/1.53  tff(c_526, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_514, c_266])).
% 3.25/1.53  tff(c_527, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_514, c_514, c_56])).
% 3.25/1.53  tff(c_528, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_526, c_527])).
% 3.25/1.53  tff(c_738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_732, c_528])).
% 3.25/1.53  tff(c_740, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_50])).
% 3.25/1.53  tff(c_739, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_50])).
% 3.25/1.53  tff(c_749, plain, ('#skF_11'='#skF_8' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_740, c_740, c_739])).
% 3.25/1.53  tff(c_750, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_749])).
% 3.25/1.53  tff(c_744, plain, (r1_xboole_0('#skF_11', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_740, c_740, c_10])).
% 3.25/1.53  tff(c_751, plain, (r1_xboole_0('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_750, c_750, c_744])).
% 3.25/1.53  tff(c_808, plain, (![A_196, B_197, C_198]: (~r1_xboole_0(A_196, B_197) | ~r2_hidden(C_198, B_197) | ~r2_hidden(C_198, A_196))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.53  tff(c_814, plain, (![C_198]: (~r2_hidden(C_198, '#skF_9'))), inference(resolution, [status(thm)], [c_751, c_808])).
% 3.25/1.53  tff(c_1064, plain, (![D_246, A_247]: (~r2_hidden(D_246, k2_zfmisc_1(A_247, '#skF_9')))), inference(resolution, [status(thm)], [c_1048, c_814])).
% 3.25/1.53  tff(c_1093, plain, (![A_248, A_249]: (r1_xboole_0(A_248, k2_zfmisc_1(A_249, '#skF_9')))), inference(resolution, [status(thm)], [c_4, c_1064])).
% 3.25/1.53  tff(c_742, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | A_7='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_740, c_12])).
% 3.25/1.53  tff(c_772, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | A_7='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_750, c_742])).
% 3.25/1.53  tff(c_1108, plain, (![A_249]: (k2_zfmisc_1(A_249, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_1093, c_772])).
% 3.25/1.53  tff(c_753, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_750, c_740])).
% 3.25/1.53  tff(c_48, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.25/1.53  tff(c_780, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_753, c_750, c_753, c_48])).
% 3.25/1.53  tff(c_1115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1108, c_780])).
% 3.25/1.53  tff(c_1116, plain, ('#skF_11'='#skF_8'), inference(splitRight, [status(thm)], [c_749])).
% 3.25/1.53  tff(c_1119, plain, (r1_xboole_0('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_1116, c_744])).
% 3.25/1.53  tff(c_1176, plain, (![A_261, B_262, C_263]: (~r1_xboole_0(A_261, B_262) | ~r2_hidden(C_263, B_262) | ~r2_hidden(C_263, A_261))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.53  tff(c_1182, plain, (![C_263]: (~r2_hidden(C_263, '#skF_8'))), inference(resolution, [status(thm)], [c_1119, c_1176])).
% 3.25/1.53  tff(c_1412, plain, (![D_306, B_307]: (~r2_hidden(D_306, k2_zfmisc_1('#skF_8', B_307)))), inference(resolution, [status(thm)], [c_1396, c_1182])).
% 3.25/1.53  tff(c_1441, plain, (![B_308, B_309]: (r1_xboole_0(k2_zfmisc_1('#skF_8', B_308), B_309))), inference(resolution, [status(thm)], [c_6, c_1412])).
% 3.25/1.53  tff(c_1139, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | A_7='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_742])).
% 3.25/1.53  tff(c_1456, plain, (![B_308]: (k2_zfmisc_1('#skF_8', B_308)='#skF_8')), inference(resolution, [status(thm)], [c_1441, c_1139])).
% 3.25/1.53  tff(c_1121, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_740])).
% 3.25/1.53  tff(c_1147, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1116, c_1121, c_48])).
% 3.25/1.53  tff(c_1463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1456, c_1147])).
% 3.25/1.53  tff(c_1465, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_54])).
% 3.25/1.53  tff(c_1464, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_54])).
% 3.25/1.53  tff(c_1482, plain, ('#skF_10'='#skF_8' | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_1465, c_1464])).
% 3.25/1.53  tff(c_1483, plain, ('#skF_10'='#skF_9'), inference(splitLeft, [status(thm)], [c_1482])).
% 3.25/1.53  tff(c_1469, plain, (r1_xboole_0('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_1465, c_10])).
% 3.25/1.53  tff(c_1485, plain, (r1_xboole_0('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1483, c_1483, c_1469])).
% 3.25/1.53  tff(c_1540, plain, (![A_322, B_323, C_324]: (~r1_xboole_0(A_322, B_323) | ~r2_hidden(C_324, B_323) | ~r2_hidden(C_324, A_322))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.53  tff(c_1546, plain, (![C_324]: (~r2_hidden(C_324, '#skF_9'))), inference(resolution, [status(thm)], [c_1485, c_1540])).
% 3.25/1.53  tff(c_1705, plain, (![D_361, A_362]: (~r2_hidden(D_361, k2_zfmisc_1(A_362, '#skF_9')))), inference(resolution, [status(thm)], [c_1696, c_1546])).
% 3.25/1.53  tff(c_1726, plain, (![A_363, A_364]: (r1_xboole_0(A_363, k2_zfmisc_1(A_364, '#skF_9')))), inference(resolution, [status(thm)], [c_4, c_1705])).
% 3.25/1.53  tff(c_1467, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | A_7='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_12])).
% 3.25/1.53  tff(c_1505, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | A_7='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1483, c_1467])).
% 3.25/1.53  tff(c_1738, plain, (![A_364]: (k2_zfmisc_1(A_364, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_1726, c_1505])).
% 3.25/1.53  tff(c_1487, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1483, c_1465])).
% 3.25/1.53  tff(c_52, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.25/1.53  tff(c_1497, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1487, c_1483, c_1487, c_52])).
% 3.25/1.53  tff(c_1744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1738, c_1497])).
% 3.25/1.53  tff(c_1745, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_1482])).
% 3.25/1.53  tff(c_1751, plain, (r1_xboole_0('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1745, c_1745, c_1469])).
% 3.25/1.53  tff(c_1806, plain, (![A_376, B_377, C_378]: (~r1_xboole_0(A_376, B_377) | ~r2_hidden(C_378, B_377) | ~r2_hidden(C_378, A_376))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.53  tff(c_1812, plain, (![C_378]: (~r2_hidden(C_378, '#skF_8'))), inference(resolution, [status(thm)], [c_1751, c_1806])).
% 3.25/1.53  tff(c_2026, plain, (![D_418, B_419]: (~r2_hidden(D_418, k2_zfmisc_1('#skF_8', B_419)))), inference(resolution, [status(thm)], [c_2013, c_1812])).
% 3.25/1.53  tff(c_2055, plain, (![B_420, B_421]: (r1_xboole_0(k2_zfmisc_1('#skF_8', B_420), B_421))), inference(resolution, [status(thm)], [c_6, c_2026])).
% 3.25/1.53  tff(c_1770, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | A_7='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1745, c_1467])).
% 3.25/1.53  tff(c_2070, plain, (![B_420]: (k2_zfmisc_1('#skF_8', B_420)='#skF_8')), inference(resolution, [status(thm)], [c_2055, c_1770])).
% 3.25/1.53  tff(c_1748, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1465, c_1465, c_52])).
% 3.25/1.53  tff(c_1749, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1745, c_1748])).
% 3.25/1.53  tff(c_2077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2070, c_1749])).
% 3.25/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.53  
% 3.25/1.53  Inference rules
% 3.25/1.53  ----------------------
% 3.25/1.53  #Ref     : 0
% 3.25/1.53  #Sup     : 412
% 3.25/1.53  #Fact    : 0
% 3.25/1.53  #Define  : 0
% 3.25/1.53  #Split   : 9
% 3.25/1.53  #Chain   : 0
% 3.25/1.53  #Close   : 0
% 3.25/1.53  
% 3.25/1.53  Ordering : KBO
% 3.25/1.53  
% 3.25/1.53  Simplification rules
% 3.25/1.53  ----------------------
% 3.25/1.53  #Subsume      : 85
% 3.25/1.53  #Demod        : 216
% 3.25/1.53  #Tautology    : 200
% 3.25/1.53  #SimpNegUnit  : 16
% 3.25/1.53  #BackRed      : 57
% 3.25/1.53  
% 3.25/1.53  #Partial instantiations: 0
% 3.25/1.53  #Strategies tried      : 1
% 3.25/1.53  
% 3.25/1.53  Timing (in seconds)
% 3.25/1.53  ----------------------
% 3.39/1.53  Preprocessing        : 0.31
% 3.39/1.53  Parsing              : 0.15
% 3.39/1.53  CNF conversion       : 0.03
% 3.39/1.53  Main loop            : 0.45
% 3.39/1.53  Inferencing          : 0.18
% 3.39/1.53  Reduction            : 0.12
% 3.39/1.53  Demodulation         : 0.08
% 3.39/1.53  BG Simplification    : 0.02
% 3.39/1.53  Subsumption          : 0.08
% 3.39/1.53  Abstraction          : 0.02
% 3.39/1.53  MUC search           : 0.00
% 3.39/1.53  Cooper               : 0.00
% 3.39/1.53  Total                : 0.80
% 3.39/1.53  Index Insertion      : 0.00
% 3.39/1.53  Index Deletion       : 0.00
% 3.39/1.53  Index Matching       : 0.00
% 3.39/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
