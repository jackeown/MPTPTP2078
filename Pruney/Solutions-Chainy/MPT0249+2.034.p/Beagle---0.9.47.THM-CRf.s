%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:28 EST 2020

% Result     : Theorem 6.92s
% Output     : CNFRefutation 7.14s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 425 expanded)
%              Number of leaves         :   32 ( 152 expanded)
%              Depth                    :   13
%              Number of atoms          :  192 ( 787 expanded)
%              Number of equality atoms :   73 ( 333 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9462,plain,(
    ! [C_395,A_396,B_397] :
      ( r1_tarski(C_395,'#skF_1'(A_396,B_397,C_395))
      | k2_xboole_0(A_396,C_395) = B_397
      | ~ r1_tarski(C_395,B_397)
      | ~ r1_tarski(A_396,B_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [B_4,A_3,C_5] :
      ( ~ r1_tarski(B_4,'#skF_1'(A_3,B_4,C_5))
      | k2_xboole_0(A_3,C_5) = B_4
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9466,plain,(
    ! [A_396,B_397] :
      ( k2_xboole_0(A_396,B_397) = B_397
      | ~ r1_tarski(B_397,B_397)
      | ~ r1_tarski(A_396,B_397) ) ),
    inference(resolution,[status(thm)],[c_9462,c_8])).

tff(c_9483,plain,(
    ! [A_398,B_399] :
      ( k2_xboole_0(A_398,B_399) = B_399
      | ~ r1_tarski(A_398,B_399) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9466])).

tff(c_9577,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_9483])).

tff(c_115,plain,(
    ! [A_72,B_73] : r1_xboole_0(k4_xboole_0(A_72,B_73),k4_xboole_0(B_73,A_72)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [A_20] :
      ( ~ r1_xboole_0(A_20,A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_132,plain,(
    ! [B_73] : k4_xboole_0(B_73,B_73) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_115,c_26])).

tff(c_6652,plain,(
    ! [A_291,B_292] : k2_xboole_0(A_291,k4_xboole_0(B_292,A_291)) = k2_xboole_0(A_291,B_292) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6677,plain,(
    ! [B_73] : k2_xboole_0(B_73,k1_xboole_0) = k2_xboole_0(B_73,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_6652])).

tff(c_14,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7086,plain,(
    ! [A_310,B_311,C_312] :
      ( r1_tarski(A_310,k2_xboole_0(B_311,C_312))
      | ~ r1_tarski(k4_xboole_0(A_310,B_311),C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_7100,plain,(
    ! [A_310,B_311] : r1_tarski(A_310,k2_xboole_0(B_311,k4_xboole_0(A_310,B_311))) ),
    inference(resolution,[status(thm)],[c_6,c_7086])).

tff(c_7105,plain,(
    ! [A_313,B_314] : r1_tarski(A_313,k2_xboole_0(B_314,A_313)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_7100])).

tff(c_7133,plain,(
    ! [B_73] : r1_tarski(k1_xboole_0,k2_xboole_0(B_73,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6677,c_7105])).

tff(c_9584,plain,(
    ! [B_73] : r1_tarski(k1_xboole_0,B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9577,c_7133])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_58,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,'#skF_1'(A_3,B_4,C_5))
      | k2_xboole_0(A_3,C_5) = B_4
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2621,plain,(
    ! [B_170,A_171,C_172] :
      ( ~ r1_tarski(B_170,'#skF_1'(A_171,B_170,C_172))
      | k2_xboole_0(A_171,C_172) = B_170
      | ~ r1_tarski(C_172,B_170)
      | ~ r1_tarski(A_171,B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2625,plain,(
    ! [B_4,C_5] :
      ( k2_xboole_0(B_4,C_5) = B_4
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(B_4,B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_2621])).

tff(c_2731,plain,(
    ! [B_175,C_176] :
      ( k2_xboole_0(B_175,C_176) = B_175
      | ~ r1_tarski(C_176,B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2625])).

tff(c_2828,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_2731])).

tff(c_176,plain,(
    ! [A_81,B_82] : k2_xboole_0(A_81,k4_xboole_0(B_82,A_81)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_201,plain,(
    ! [B_73] : k2_xboole_0(B_73,k1_xboole_0) = k2_xboole_0(B_73,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_176])).

tff(c_549,plain,(
    ! [A_94,B_95,C_96] :
      ( r1_tarski(A_94,k2_xboole_0(B_95,C_96))
      | ~ r1_tarski(k4_xboole_0(A_94,B_95),C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_566,plain,(
    ! [A_94,B_95] : r1_tarski(A_94,k2_xboole_0(B_95,k4_xboole_0(A_94,B_95))) ),
    inference(resolution,[status(thm)],[c_6,c_549])).

tff(c_571,plain,(
    ! [A_97,B_98] : r1_tarski(A_97,k2_xboole_0(B_98,A_97)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_566])).

tff(c_602,plain,(
    ! [B_73] : r1_tarski(k1_xboole_0,k2_xboole_0(B_73,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_571])).

tff(c_2909,plain,(
    ! [B_73] : r1_tarski(k1_xboole_0,B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2828,c_602])).

tff(c_52,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k1_tarski(A_55),B_56)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_60,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_608,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_571])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_617,plain,
    ( k1_tarski('#skF_2') = '#skF_4'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_608,c_2])).

tff(c_761,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_765,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_761])).

tff(c_48,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(k1_tarski(A_53),B_54)
      | r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_77,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k2_xboole_0(A_61,B_62)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_84,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_77])).

tff(c_1590,plain,(
    ! [C_134,B_135,A_136] :
      ( k4_xboole_0(k2_xboole_0(C_134,B_135),A_136) = k2_xboole_0(k4_xboole_0(C_134,A_136),B_135)
      | ~ r1_xboole_0(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1706,plain,(
    ! [A_137] :
      ( k4_xboole_0(k1_tarski('#skF_2'),A_137) = k2_xboole_0(k4_xboole_0('#skF_3',A_137),'#skF_4')
      | ~ r1_xboole_0(A_137,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1590])).

tff(c_1752,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_3',k1_tarski('#skF_2')),'#skF_4') = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski('#skF_2'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1706,c_132])).

tff(c_1782,plain,
    ( k2_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1752])).

tff(c_2259,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1782])).

tff(c_2262,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_2259])).

tff(c_2266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_765,c_2262])).

tff(c_2267,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1782])).

tff(c_570,plain,(
    ! [A_94,B_95] : r1_tarski(A_94,k2_xboole_0(B_95,A_94)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_566])).

tff(c_2298,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2267,c_570])).

tff(c_2347,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_2298,c_2])).

tff(c_2350,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2347])).

tff(c_3078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2909,c_2350])).

tff(c_3079,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_3753,plain,(
    ! [B_195] :
      ( r1_xboole_0('#skF_4',B_195)
      | r2_hidden('#skF_2',B_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3079,c_48])).

tff(c_30,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_73,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_30])).

tff(c_159,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(B_79,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_169,plain,
    ( k1_tarski('#skF_2') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_159])).

tff(c_175,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_218,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_175])).

tff(c_3757,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_3753,c_218])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( r1_tarski(C_5,'#skF_1'(A_3,B_4,C_5))
      | k2_xboole_0(A_3,C_5) = B_4
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4892,plain,(
    ! [B_256,A_257,C_258] :
      ( ~ r1_tarski(B_256,'#skF_1'(A_257,B_256,C_258))
      | k2_xboole_0(A_257,C_258) = B_256
      | ~ r1_tarski(C_258,B_256)
      | ~ r1_tarski(A_257,B_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4896,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(B_4,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_4892])).

tff(c_4912,plain,(
    ! [A_259,B_260] :
      ( k2_xboole_0(A_259,B_260) = B_260
      | ~ r1_tarski(A_259,B_260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4896])).

tff(c_4991,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_4912])).

tff(c_5172,plain,(
    ! [B_262] : r1_tarski(k1_xboole_0,B_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4991,c_602])).

tff(c_4907,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4896])).

tff(c_5182,plain,(
    ! [B_262] : k2_xboole_0(k1_xboole_0,B_262) = B_262 ),
    inference(resolution,[status(thm)],[c_5172,c_4907])).

tff(c_20,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_638,plain,(
    ! [A_102,B_103,C_104] : k4_xboole_0(k4_xboole_0(A_102,B_103),C_104) = k4_xboole_0(A_102,k2_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_673,plain,(
    ! [B_73,C_104] : k4_xboole_0(B_73,k2_xboole_0(B_73,C_104)) = k4_xboole_0(k1_xboole_0,C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_638])).

tff(c_693,plain,(
    ! [C_104] : k4_xboole_0(k1_xboole_0,C_104) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_673])).

tff(c_5508,plain,(
    ! [B_266] : k2_xboole_0(k1_xboole_0,B_266) = B_266 ),
    inference(resolution,[status(thm)],[c_5172,c_4907])).

tff(c_34,plain,(
    ! [C_29,B_28,A_27] :
      ( k4_xboole_0(k2_xboole_0(C_29,B_28),A_27) = k2_xboole_0(k4_xboole_0(C_29,A_27),B_28)
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5546,plain,(
    ! [A_27,B_266] :
      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,A_27),B_266) = k4_xboole_0(B_266,A_27)
      | ~ r1_xboole_0(A_27,B_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5508,c_34])).

tff(c_6592,plain,(
    ! [B_289,A_290] :
      ( k4_xboole_0(B_289,A_290) = B_289
      | ~ r1_xboole_0(A_290,B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5182,c_693,c_5546])).

tff(c_6616,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3757,c_6592])).

tff(c_3088,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3079,c_84])).

tff(c_6619,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6616,c_3088])).

tff(c_6621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6619])).

tff(c_6622,plain,(
    k1_tarski('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_6628,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6622,c_60])).

tff(c_7136,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6628,c_7105])).

tff(c_7147,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_7136,c_2])).

tff(c_7150,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7147])).

tff(c_6648,plain,(
    ! [B_54] :
      ( r1_xboole_0('#skF_3',B_54)
      | r2_hidden('#skF_2',B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6622,c_48])).

tff(c_6778,plain,(
    ! [B_296] :
      ( r1_tarski('#skF_3',B_296)
      | ~ r2_hidden('#skF_2',B_296) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6622,c_52])).

tff(c_6796,plain,(
    ! [B_54] :
      ( r1_tarski('#skF_3',B_54)
      | r1_xboole_0('#skF_3',B_54) ) ),
    inference(resolution,[status(thm)],[c_6648,c_6778])).

tff(c_7898,plain,(
    ! [C_336,B_337,A_338] :
      ( k4_xboole_0(k2_xboole_0(C_336,B_337),A_338) = k2_xboole_0(k4_xboole_0(C_336,A_338),B_337)
      | ~ r1_xboole_0(A_338,B_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8007,plain,(
    ! [A_339] :
      ( k2_xboole_0(k4_xboole_0('#skF_3',A_339),'#skF_4') = k4_xboole_0('#skF_3',A_339)
      | ~ r1_xboole_0(A_339,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6628,c_7898])).

tff(c_8051,plain,
    ( k4_xboole_0('#skF_3','#skF_3') = k2_xboole_0(k1_xboole_0,'#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_8007])).

tff(c_8067,plain,
    ( k2_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_8051])).

tff(c_8972,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8067])).

tff(c_9022,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6796,c_8972])).

tff(c_9026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7150,c_9022])).

tff(c_9027,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8067])).

tff(c_7104,plain,(
    ! [A_310,B_311] : r1_tarski(A_310,k2_xboole_0(B_311,A_310)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_7100])).

tff(c_9056,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9027,c_7104])).

tff(c_9090,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_9056,c_2])).

tff(c_9093,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_9090])).

tff(c_9789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9584,c_9093])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.92/2.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.92/2.39  
% 6.92/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.92/2.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 6.92/2.40  
% 6.92/2.40  %Foreground sorts:
% 6.92/2.40  
% 6.92/2.40  
% 6.92/2.40  %Background operators:
% 6.92/2.40  
% 6.92/2.40  
% 6.92/2.40  %Foreground operators:
% 6.92/2.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.92/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.92/2.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.92/2.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.92/2.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.92/2.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.92/2.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.92/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.92/2.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.92/2.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.92/2.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.92/2.40  tff('#skF_2', type, '#skF_2': $i).
% 6.92/2.40  tff('#skF_3', type, '#skF_3': $i).
% 6.92/2.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.92/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.92/2.40  tff('#skF_4', type, '#skF_4': $i).
% 6.92/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.92/2.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.92/2.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.92/2.40  
% 7.14/2.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.14/2.42  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 7.14/2.42  tff(f_74, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 7.14/2.42  tff(f_68, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 7.14/2.42  tff(f_46, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.14/2.42  tff(f_52, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 7.14/2.42  tff(f_112, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 7.14/2.42  tff(f_99, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 7.14/2.42  tff(f_95, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.14/2.42  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.14/2.42  tff(f_78, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 7.14/2.42  tff(f_72, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.14/2.42  tff(f_48, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.14/2.42  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.14/2.42  tff(c_9462, plain, (![C_395, A_396, B_397]: (r1_tarski(C_395, '#skF_1'(A_396, B_397, C_395)) | k2_xboole_0(A_396, C_395)=B_397 | ~r1_tarski(C_395, B_397) | ~r1_tarski(A_396, B_397))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.14/2.42  tff(c_8, plain, (![B_4, A_3, C_5]: (~r1_tarski(B_4, '#skF_1'(A_3, B_4, C_5)) | k2_xboole_0(A_3, C_5)=B_4 | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.14/2.42  tff(c_9466, plain, (![A_396, B_397]: (k2_xboole_0(A_396, B_397)=B_397 | ~r1_tarski(B_397, B_397) | ~r1_tarski(A_396, B_397))), inference(resolution, [status(thm)], [c_9462, c_8])).
% 7.14/2.42  tff(c_9483, plain, (![A_398, B_399]: (k2_xboole_0(A_398, B_399)=B_399 | ~r1_tarski(A_398, B_399))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9466])).
% 7.14/2.42  tff(c_9577, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_9483])).
% 7.14/2.42  tff(c_115, plain, (![A_72, B_73]: (r1_xboole_0(k4_xboole_0(A_72, B_73), k4_xboole_0(B_73, A_72)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.14/2.42  tff(c_26, plain, (![A_20]: (~r1_xboole_0(A_20, A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.14/2.42  tff(c_132, plain, (![B_73]: (k4_xboole_0(B_73, B_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_115, c_26])).
% 7.14/2.42  tff(c_6652, plain, (![A_291, B_292]: (k2_xboole_0(A_291, k4_xboole_0(B_292, A_291))=k2_xboole_0(A_291, B_292))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.14/2.42  tff(c_6677, plain, (![B_73]: (k2_xboole_0(B_73, k1_xboole_0)=k2_xboole_0(B_73, B_73))), inference(superposition, [status(thm), theory('equality')], [c_132, c_6652])).
% 7.14/2.42  tff(c_14, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.14/2.42  tff(c_7086, plain, (![A_310, B_311, C_312]: (r1_tarski(A_310, k2_xboole_0(B_311, C_312)) | ~r1_tarski(k4_xboole_0(A_310, B_311), C_312))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.14/2.42  tff(c_7100, plain, (![A_310, B_311]: (r1_tarski(A_310, k2_xboole_0(B_311, k4_xboole_0(A_310, B_311))))), inference(resolution, [status(thm)], [c_6, c_7086])).
% 7.14/2.42  tff(c_7105, plain, (![A_313, B_314]: (r1_tarski(A_313, k2_xboole_0(B_314, A_313)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_7100])).
% 7.14/2.42  tff(c_7133, plain, (![B_73]: (r1_tarski(k1_xboole_0, k2_xboole_0(B_73, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_6677, c_7105])).
% 7.14/2.42  tff(c_9584, plain, (![B_73]: (r1_tarski(k1_xboole_0, B_73))), inference(demodulation, [status(thm), theory('equality')], [c_9577, c_7133])).
% 7.14/2.42  tff(c_54, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.14/2.42  tff(c_58, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.14/2.42  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.14/2.42  tff(c_12, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, '#skF_1'(A_3, B_4, C_5)) | k2_xboole_0(A_3, C_5)=B_4 | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.14/2.42  tff(c_2621, plain, (![B_170, A_171, C_172]: (~r1_tarski(B_170, '#skF_1'(A_171, B_170, C_172)) | k2_xboole_0(A_171, C_172)=B_170 | ~r1_tarski(C_172, B_170) | ~r1_tarski(A_171, B_170))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.14/2.42  tff(c_2625, plain, (![B_4, C_5]: (k2_xboole_0(B_4, C_5)=B_4 | ~r1_tarski(C_5, B_4) | ~r1_tarski(B_4, B_4))), inference(resolution, [status(thm)], [c_12, c_2621])).
% 7.14/2.42  tff(c_2731, plain, (![B_175, C_176]: (k2_xboole_0(B_175, C_176)=B_175 | ~r1_tarski(C_176, B_175))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2625])).
% 7.14/2.42  tff(c_2828, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_2731])).
% 7.14/2.42  tff(c_176, plain, (![A_81, B_82]: (k2_xboole_0(A_81, k4_xboole_0(B_82, A_81))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.14/2.42  tff(c_201, plain, (![B_73]: (k2_xboole_0(B_73, k1_xboole_0)=k2_xboole_0(B_73, B_73))), inference(superposition, [status(thm), theory('equality')], [c_132, c_176])).
% 7.14/2.42  tff(c_549, plain, (![A_94, B_95, C_96]: (r1_tarski(A_94, k2_xboole_0(B_95, C_96)) | ~r1_tarski(k4_xboole_0(A_94, B_95), C_96))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.14/2.42  tff(c_566, plain, (![A_94, B_95]: (r1_tarski(A_94, k2_xboole_0(B_95, k4_xboole_0(A_94, B_95))))), inference(resolution, [status(thm)], [c_6, c_549])).
% 7.14/2.42  tff(c_571, plain, (![A_97, B_98]: (r1_tarski(A_97, k2_xboole_0(B_98, A_97)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_566])).
% 7.14/2.42  tff(c_602, plain, (![B_73]: (r1_tarski(k1_xboole_0, k2_xboole_0(B_73, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_201, c_571])).
% 7.14/2.42  tff(c_2909, plain, (![B_73]: (r1_tarski(k1_xboole_0, B_73))), inference(demodulation, [status(thm), theory('equality')], [c_2828, c_602])).
% 7.14/2.42  tff(c_52, plain, (![A_55, B_56]: (r1_tarski(k1_tarski(A_55), B_56) | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.14/2.42  tff(c_60, plain, (k2_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.14/2.42  tff(c_608, plain, (r1_tarski('#skF_4', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_571])).
% 7.14/2.42  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.14/2.42  tff(c_617, plain, (k1_tarski('#skF_2')='#skF_4' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_608, c_2])).
% 7.14/2.42  tff(c_761, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_617])).
% 7.14/2.42  tff(c_765, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_761])).
% 7.14/2.42  tff(c_48, plain, (![A_53, B_54]: (r1_xboole_0(k1_tarski(A_53), B_54) | r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.14/2.42  tff(c_77, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k2_xboole_0(A_61, B_62))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.14/2.42  tff(c_84, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_60, c_77])).
% 7.14/2.42  tff(c_1590, plain, (![C_134, B_135, A_136]: (k4_xboole_0(k2_xboole_0(C_134, B_135), A_136)=k2_xboole_0(k4_xboole_0(C_134, A_136), B_135) | ~r1_xboole_0(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.14/2.42  tff(c_1706, plain, (![A_137]: (k4_xboole_0(k1_tarski('#skF_2'), A_137)=k2_xboole_0(k4_xboole_0('#skF_3', A_137), '#skF_4') | ~r1_xboole_0(A_137, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1590])).
% 7.14/2.42  tff(c_1752, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k1_tarski('#skF_2')), '#skF_4')=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_2'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1706, c_132])).
% 7.14/2.42  tff(c_1782, plain, (k2_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0 | ~r1_xboole_0(k1_tarski('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1752])).
% 7.14/2.42  tff(c_2259, plain, (~r1_xboole_0(k1_tarski('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1782])).
% 7.14/2.42  tff(c_2262, plain, (r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_2259])).
% 7.14/2.42  tff(c_2266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_765, c_2262])).
% 7.14/2.42  tff(c_2267, plain, (k2_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1782])).
% 7.14/2.42  tff(c_570, plain, (![A_94, B_95]: (r1_tarski(A_94, k2_xboole_0(B_95, A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_566])).
% 7.14/2.42  tff(c_2298, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2267, c_570])).
% 7.14/2.42  tff(c_2347, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_2298, c_2])).
% 7.14/2.42  tff(c_2350, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_2347])).
% 7.14/2.42  tff(c_3078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2909, c_2350])).
% 7.14/2.42  tff(c_3079, plain, (k1_tarski('#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_617])).
% 7.14/2.42  tff(c_3753, plain, (![B_195]: (r1_xboole_0('#skF_4', B_195) | r2_hidden('#skF_2', B_195))), inference(superposition, [status(thm), theory('equality')], [c_3079, c_48])).
% 7.14/2.42  tff(c_30, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.14/2.42  tff(c_73, plain, (r1_tarski('#skF_3', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_30])).
% 7.14/2.42  tff(c_159, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(B_79, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.14/2.42  tff(c_169, plain, (k1_tarski('#skF_2')='#skF_3' | ~r1_tarski(k1_tarski('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_73, c_159])).
% 7.14/2.42  tff(c_175, plain, (~r1_tarski(k1_tarski('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_169])).
% 7.14/2.42  tff(c_218, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_175])).
% 7.14/2.42  tff(c_3757, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_3753, c_218])).
% 7.14/2.42  tff(c_10, plain, (![C_5, A_3, B_4]: (r1_tarski(C_5, '#skF_1'(A_3, B_4, C_5)) | k2_xboole_0(A_3, C_5)=B_4 | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.14/2.42  tff(c_4892, plain, (![B_256, A_257, C_258]: (~r1_tarski(B_256, '#skF_1'(A_257, B_256, C_258)) | k2_xboole_0(A_257, C_258)=B_256 | ~r1_tarski(C_258, B_256) | ~r1_tarski(A_257, B_256))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.14/2.42  tff(c_4896, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(B_4, B_4) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_10, c_4892])).
% 7.14/2.42  tff(c_4912, plain, (![A_259, B_260]: (k2_xboole_0(A_259, B_260)=B_260 | ~r1_tarski(A_259, B_260))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4896])).
% 7.14/2.42  tff(c_4991, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_4912])).
% 7.14/2.42  tff(c_5172, plain, (![B_262]: (r1_tarski(k1_xboole_0, B_262))), inference(demodulation, [status(thm), theory('equality')], [c_4991, c_602])).
% 7.14/2.42  tff(c_4907, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4896])).
% 7.14/2.42  tff(c_5182, plain, (![B_262]: (k2_xboole_0(k1_xboole_0, B_262)=B_262)), inference(resolution, [status(thm)], [c_5172, c_4907])).
% 7.14/2.42  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.14/2.42  tff(c_638, plain, (![A_102, B_103, C_104]: (k4_xboole_0(k4_xboole_0(A_102, B_103), C_104)=k4_xboole_0(A_102, k2_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.14/2.42  tff(c_673, plain, (![B_73, C_104]: (k4_xboole_0(B_73, k2_xboole_0(B_73, C_104))=k4_xboole_0(k1_xboole_0, C_104))), inference(superposition, [status(thm), theory('equality')], [c_132, c_638])).
% 7.14/2.42  tff(c_693, plain, (![C_104]: (k4_xboole_0(k1_xboole_0, C_104)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_673])).
% 7.14/2.42  tff(c_5508, plain, (![B_266]: (k2_xboole_0(k1_xboole_0, B_266)=B_266)), inference(resolution, [status(thm)], [c_5172, c_4907])).
% 7.14/2.42  tff(c_34, plain, (![C_29, B_28, A_27]: (k4_xboole_0(k2_xboole_0(C_29, B_28), A_27)=k2_xboole_0(k4_xboole_0(C_29, A_27), B_28) | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.14/2.42  tff(c_5546, plain, (![A_27, B_266]: (k2_xboole_0(k4_xboole_0(k1_xboole_0, A_27), B_266)=k4_xboole_0(B_266, A_27) | ~r1_xboole_0(A_27, B_266))), inference(superposition, [status(thm), theory('equality')], [c_5508, c_34])).
% 7.14/2.42  tff(c_6592, plain, (![B_289, A_290]: (k4_xboole_0(B_289, A_290)=B_289 | ~r1_xboole_0(A_290, B_289))), inference(demodulation, [status(thm), theory('equality')], [c_5182, c_693, c_5546])).
% 7.14/2.42  tff(c_6616, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_3757, c_6592])).
% 7.14/2.42  tff(c_3088, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3079, c_84])).
% 7.14/2.42  tff(c_6619, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6616, c_3088])).
% 7.14/2.42  tff(c_6621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_6619])).
% 7.14/2.42  tff(c_6622, plain, (k1_tarski('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_169])).
% 7.14/2.42  tff(c_6628, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6622, c_60])).
% 7.14/2.42  tff(c_7136, plain, (r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6628, c_7105])).
% 7.14/2.42  tff(c_7147, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_7136, c_2])).
% 7.14/2.42  tff(c_7150, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_7147])).
% 7.14/2.42  tff(c_6648, plain, (![B_54]: (r1_xboole_0('#skF_3', B_54) | r2_hidden('#skF_2', B_54))), inference(superposition, [status(thm), theory('equality')], [c_6622, c_48])).
% 7.14/2.42  tff(c_6778, plain, (![B_296]: (r1_tarski('#skF_3', B_296) | ~r2_hidden('#skF_2', B_296))), inference(superposition, [status(thm), theory('equality')], [c_6622, c_52])).
% 7.14/2.42  tff(c_6796, plain, (![B_54]: (r1_tarski('#skF_3', B_54) | r1_xboole_0('#skF_3', B_54))), inference(resolution, [status(thm)], [c_6648, c_6778])).
% 7.14/2.42  tff(c_7898, plain, (![C_336, B_337, A_338]: (k4_xboole_0(k2_xboole_0(C_336, B_337), A_338)=k2_xboole_0(k4_xboole_0(C_336, A_338), B_337) | ~r1_xboole_0(A_338, B_337))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.14/2.42  tff(c_8007, plain, (![A_339]: (k2_xboole_0(k4_xboole_0('#skF_3', A_339), '#skF_4')=k4_xboole_0('#skF_3', A_339) | ~r1_xboole_0(A_339, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6628, c_7898])).
% 7.14/2.42  tff(c_8051, plain, (k4_xboole_0('#skF_3', '#skF_3')=k2_xboole_0(k1_xboole_0, '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_132, c_8007])).
% 7.14/2.42  tff(c_8067, plain, (k2_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0 | ~r1_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_8051])).
% 7.14/2.42  tff(c_8972, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_8067])).
% 7.14/2.42  tff(c_9022, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6796, c_8972])).
% 7.14/2.42  tff(c_9026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7150, c_9022])).
% 7.14/2.42  tff(c_9027, plain, (k2_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8067])).
% 7.14/2.42  tff(c_7104, plain, (![A_310, B_311]: (r1_tarski(A_310, k2_xboole_0(B_311, A_310)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_7100])).
% 7.14/2.42  tff(c_9056, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9027, c_7104])).
% 7.14/2.42  tff(c_9090, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_9056, c_2])).
% 7.14/2.42  tff(c_9093, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_9090])).
% 7.14/2.42  tff(c_9789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9584, c_9093])).
% 7.14/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.14/2.42  
% 7.14/2.42  Inference rules
% 7.14/2.42  ----------------------
% 7.14/2.42  #Ref     : 0
% 7.14/2.42  #Sup     : 2401
% 7.14/2.42  #Fact    : 0
% 7.14/2.42  #Define  : 0
% 7.14/2.42  #Split   : 5
% 7.14/2.42  #Chain   : 0
% 7.14/2.42  #Close   : 0
% 7.14/2.42  
% 7.14/2.42  Ordering : KBO
% 7.14/2.42  
% 7.14/2.42  Simplification rules
% 7.14/2.42  ----------------------
% 7.14/2.42  #Subsume      : 37
% 7.14/2.42  #Demod        : 2012
% 7.14/2.42  #Tautology    : 1353
% 7.14/2.42  #SimpNegUnit  : 14
% 7.14/2.42  #BackRed      : 59
% 7.14/2.42  
% 7.14/2.42  #Partial instantiations: 0
% 7.14/2.42  #Strategies tried      : 1
% 7.14/2.42  
% 7.14/2.42  Timing (in seconds)
% 7.14/2.42  ----------------------
% 7.14/2.42  Preprocessing        : 0.33
% 7.14/2.42  Parsing              : 0.17
% 7.14/2.42  CNF conversion       : 0.02
% 7.14/2.42  Main loop            : 1.31
% 7.14/2.42  Inferencing          : 0.39
% 7.14/2.42  Reduction            : 0.56
% 7.14/2.42  Demodulation         : 0.45
% 7.14/2.42  BG Simplification    : 0.05
% 7.14/2.42  Subsumption          : 0.21
% 7.14/2.42  Abstraction          : 0.06
% 7.14/2.42  MUC search           : 0.00
% 7.14/2.42  Cooper               : 0.00
% 7.14/2.42  Total                : 1.68
% 7.14/2.42  Index Insertion      : 0.00
% 7.14/2.42  Index Deletion       : 0.00
% 7.14/2.42  Index Matching       : 0.00
% 7.14/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
