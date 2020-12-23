%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:33 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 251 expanded)
%              Number of leaves         :   30 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  169 ( 463 expanded)
%              Number of equality atoms :   52 ( 174 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_59,axiom,(
    ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
      <=> ( r2_hidden(A,B)
          & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_53,axiom,(
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

tff(c_889,plain,(
    ! [A_214,B_215,C_216,D_217] : k3_enumset1(A_214,A_214,B_215,C_216,D_217) = k2_enumset1(A_214,B_215,C_216,D_217) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    ! [A_18] : k3_enumset1(A_18,A_18,A_18,A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_906,plain,(
    ! [D_218] : k2_enumset1(D_218,D_218,D_218,D_218) = k1_tarski(D_218) ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_30])).

tff(c_28,plain,(
    ! [A_16,B_17] : k2_enumset1(A_16,A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_922,plain,(
    ! [D_219] : k2_tarski(D_219,D_219) = k1_tarski(D_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_28])).

tff(c_34,plain,(
    ! [B_20,C_21] : r1_tarski(k2_tarski(B_20,C_21),k2_tarski(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_822,plain,(
    ! [B_192,C_193,A_194] :
      ( r2_hidden(B_192,C_193)
      | ~ r1_tarski(k2_tarski(A_194,B_192),C_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_826,plain,(
    ! [C_21,B_20] : r2_hidden(C_21,k2_tarski(B_20,C_21)) ),
    inference(resolution,[status(thm)],[c_34,c_822])).

tff(c_928,plain,(
    ! [D_219] : r2_hidden(D_219,k1_tarski(D_219)) ),
    inference(superposition,[status(thm),theory(equality)],[c_922,c_826])).

tff(c_52,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( '#skF_6' != '#skF_4'
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_73,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_171,plain,(
    ! [A_74,B_75,C_76,D_77] : k3_enumset1(A_74,A_74,B_75,C_76,D_77) = k2_enumset1(A_74,B_75,C_76,D_77) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_187,plain,(
    ! [D_78] : k2_enumset1(D_78,D_78,D_78,D_78) = k1_tarski(D_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_30])).

tff(c_203,plain,(
    ! [D_79] : k2_tarski(D_79,D_79) = k1_tarski(D_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_28])).

tff(c_116,plain,(
    ! [B_55,C_56,A_57] :
      ( r2_hidden(B_55,C_56)
      | ~ r1_tarski(k2_tarski(A_57,B_55),C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_120,plain,(
    ! [C_21,B_20] : r2_hidden(C_21,k2_tarski(B_20,C_21)) ),
    inference(resolution,[status(thm)],[c_34,c_116])).

tff(c_212,plain,(
    ! [D_79] : r2_hidden(D_79,k1_tarski(D_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_120])).

tff(c_60,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_121,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_121,c_6])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_125])).

tff(c_133,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_134,plain,(
    ~ r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_248,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_56])).

tff(c_251,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_248])).

tff(c_254,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_251])).

tff(c_42,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(k1_tarski(A_22),k1_tarski(B_23))
      | B_23 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_136,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_64,B_63)
      | ~ r2_hidden(C_64,A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_139,plain,(
    ! [C_64,B_23,A_22] :
      ( ~ r2_hidden(C_64,k1_tarski(B_23))
      | ~ r2_hidden(C_64,k1_tarski(A_22))
      | B_23 = A_22 ) ),
    inference(resolution,[status(thm)],[c_42,c_136])).

tff(c_260,plain,(
    ! [A_82] :
      ( ~ r2_hidden('#skF_4',k1_tarski(A_82))
      | A_82 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_254,c_139])).

tff(c_267,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_212,c_260])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_267])).

tff(c_274,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_285,plain,(
    ! [D_85,A_86,B_87] :
      ( r2_hidden(D_85,A_86)
      | ~ r2_hidden(D_85,k4_xboole_0(A_86,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_288,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_274,c_285])).

tff(c_292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_288])).

tff(c_293,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_295,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_670,plain,(
    ! [A_165,B_166,C_167,D_168] : k3_enumset1(A_165,A_165,B_166,C_167,D_168) = k2_enumset1(A_165,B_166,C_167,D_168) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_686,plain,(
    ! [D_169] : k2_enumset1(D_169,D_169,D_169,D_169) = k1_tarski(D_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_30])).

tff(c_702,plain,(
    ! [D_170] : k2_tarski(D_170,D_170) = k1_tarski(D_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_686,c_28])).

tff(c_320,plain,(
    ! [A_103,C_104,B_105] :
      ( r2_hidden(A_103,C_104)
      | ~ r1_tarski(k2_tarski(A_103,B_105),C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_324,plain,(
    ! [B_20,C_21] : r2_hidden(B_20,k2_tarski(B_20,C_21)) ),
    inference(resolution,[status(thm)],[c_34,c_320])).

tff(c_711,plain,(
    ! [D_170] : r2_hidden(D_170,k1_tarski(D_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_324])).

tff(c_525,plain,(
    ! [A_141,B_142,C_143,D_144] : k3_enumset1(A_141,A_141,B_142,C_143,D_144) = k2_enumset1(A_141,B_142,C_143,D_144) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_541,plain,(
    ! [D_145] : k2_enumset1(D_145,D_145,D_145,D_145) = k1_tarski(D_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_30])).

tff(c_557,plain,(
    ! [D_146] : k2_tarski(D_146,D_146) = k1_tarski(D_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_28])).

tff(c_605,plain,(
    ! [D_151] : r2_hidden(D_151,k1_tarski(D_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_324])).

tff(c_386,plain,(
    ! [A_121,B_122,C_123,D_124] : k3_enumset1(A_121,A_121,B_122,C_123,D_124) = k2_enumset1(A_121,B_122,C_123,D_124) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_402,plain,(
    ! [D_125] : k2_enumset1(D_125,D_125,D_125,D_125) = k1_tarski(D_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_30])).

tff(c_418,plain,(
    ! [D_126] : k2_tarski(D_126,D_126) = k1_tarski(D_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_28])).

tff(c_424,plain,(
    ! [D_126] : r2_hidden(D_126,k1_tarski(D_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_324])).

tff(c_294,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_54,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_333,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_54])).

tff(c_334,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_360,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_60])).

tff(c_361,plain,(
    r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_368,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_361,c_4])).

tff(c_457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_368])).

tff(c_458,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_477,plain,(
    ! [D_133,A_134,B_135] :
      ( r2_hidden(D_133,k4_xboole_0(A_134,B_135))
      | r2_hidden(D_133,B_135)
      | ~ r2_hidden(D_133,A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_459,plain,(
    ~ r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_475,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_56])).

tff(c_476,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_475])).

tff(c_480,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_477,c_476])).

tff(c_492,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_480])).

tff(c_460,plain,(
    ! [A_127,B_128,C_129] :
      ( ~ r1_xboole_0(A_127,B_128)
      | ~ r2_hidden(C_129,B_128)
      | ~ r2_hidden(C_129,A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_463,plain,(
    ! [C_129,B_23,A_22] :
      ( ~ r2_hidden(C_129,k1_tarski(B_23))
      | ~ r2_hidden(C_129,k1_tarski(A_22))
      | B_23 = A_22 ) ),
    inference(resolution,[status(thm)],[c_42,c_460])).

tff(c_500,plain,(
    ! [A_22] :
      ( ~ r2_hidden('#skF_4',k1_tarski(A_22))
      | A_22 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_492,c_463])).

tff(c_613,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_605,c_500])).

tff(c_621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_613])).

tff(c_622,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_746,plain,(
    ! [D_172,A_173,B_174] :
      ( r2_hidden(D_172,k4_xboole_0(A_173,B_174))
      | r2_hidden(D_172,B_174)
      | ~ r2_hidden(D_172,A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_623,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_659,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_50])).

tff(c_660,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_623,c_659])).

tff(c_749,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_746,c_660])).

tff(c_758,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_749])).

tff(c_644,plain,(
    ! [A_156,B_157,C_158] :
      ( ~ r1_xboole_0(A_156,B_157)
      | ~ r2_hidden(C_158,B_157)
      | ~ r2_hidden(C_158,A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_647,plain,(
    ! [C_158,B_23,A_22] :
      ( ~ r2_hidden(C_158,k1_tarski(B_23))
      | ~ r2_hidden(C_158,k1_tarski(A_22))
      | B_23 = A_22 ) ),
    inference(resolution,[status(thm)],[c_42,c_644])).

tff(c_770,plain,(
    ! [A_177] :
      ( ~ r2_hidden('#skF_4',k1_tarski(A_177))
      | A_177 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_758,c_647])).

tff(c_777,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_711,c_770])).

tff(c_783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_777])).

tff(c_784,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_785,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_816,plain,(
    r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_785,c_58])).

tff(c_844,plain,(
    ! [D_200,B_201,A_202] :
      ( ~ r2_hidden(D_200,B_201)
      | ~ r2_hidden(D_200,k4_xboole_0(A_202,B_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_853,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_816,c_844])).

tff(c_961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_853])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.48  
% 3.05/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 3.05/1.48  
% 3.05/1.48  %Foreground sorts:
% 3.05/1.48  
% 3.05/1.48  
% 3.05/1.48  %Background operators:
% 3.05/1.48  
% 3.05/1.48  
% 3.05/1.48  %Foreground operators:
% 3.05/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.05/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.05/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.05/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.05/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.05/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.05/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.05/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.05/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.05/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.05/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.05/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.05/1.48  tff('#skF_9', type, '#skF_9': $i).
% 3.05/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.05/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.48  
% 3.05/1.50  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.05/1.50  tff(f_59, axiom, (![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_enumset1)).
% 3.05/1.50  tff(f_57, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 3.05/1.50  tff(f_74, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.05/1.50  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.05/1.50  tff(f_93, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.05/1.50  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.05/1.50  tff(f_79, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 3.05/1.50  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.05/1.50  tff(c_889, plain, (![A_214, B_215, C_216, D_217]: (k3_enumset1(A_214, A_214, B_215, C_216, D_217)=k2_enumset1(A_214, B_215, C_216, D_217))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.05/1.50  tff(c_30, plain, (![A_18]: (k3_enumset1(A_18, A_18, A_18, A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.05/1.50  tff(c_906, plain, (![D_218]: (k2_enumset1(D_218, D_218, D_218, D_218)=k1_tarski(D_218))), inference(superposition, [status(thm), theory('equality')], [c_889, c_30])).
% 3.05/1.50  tff(c_28, plain, (![A_16, B_17]: (k2_enumset1(A_16, A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.05/1.50  tff(c_922, plain, (![D_219]: (k2_tarski(D_219, D_219)=k1_tarski(D_219))), inference(superposition, [status(thm), theory('equality')], [c_906, c_28])).
% 3.05/1.50  tff(c_34, plain, (![B_20, C_21]: (r1_tarski(k2_tarski(B_20, C_21), k2_tarski(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.05/1.50  tff(c_822, plain, (![B_192, C_193, A_194]: (r2_hidden(B_192, C_193) | ~r1_tarski(k2_tarski(A_194, B_192), C_193))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.05/1.50  tff(c_826, plain, (![C_21, B_20]: (r2_hidden(C_21, k2_tarski(B_20, C_21)))), inference(resolution, [status(thm)], [c_34, c_822])).
% 3.05/1.50  tff(c_928, plain, (![D_219]: (r2_hidden(D_219, k1_tarski(D_219)))), inference(superposition, [status(thm), theory('equality')], [c_922, c_826])).
% 3.05/1.50  tff(c_52, plain, ('#skF_6'!='#skF_4' | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.05/1.50  tff(c_64, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_52])).
% 3.05/1.50  tff(c_58, plain, ('#skF_6'!='#skF_4' | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.05/1.50  tff(c_73, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_58])).
% 3.05/1.50  tff(c_171, plain, (![A_74, B_75, C_76, D_77]: (k3_enumset1(A_74, A_74, B_75, C_76, D_77)=k2_enumset1(A_74, B_75, C_76, D_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.05/1.50  tff(c_187, plain, (![D_78]: (k2_enumset1(D_78, D_78, D_78, D_78)=k1_tarski(D_78))), inference(superposition, [status(thm), theory('equality')], [c_171, c_30])).
% 3.05/1.50  tff(c_203, plain, (![D_79]: (k2_tarski(D_79, D_79)=k1_tarski(D_79))), inference(superposition, [status(thm), theory('equality')], [c_187, c_28])).
% 3.05/1.50  tff(c_116, plain, (![B_55, C_56, A_57]: (r2_hidden(B_55, C_56) | ~r1_tarski(k2_tarski(A_57, B_55), C_56))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.05/1.50  tff(c_120, plain, (![C_21, B_20]: (r2_hidden(C_21, k2_tarski(B_20, C_21)))), inference(resolution, [status(thm)], [c_34, c_116])).
% 3.05/1.50  tff(c_212, plain, (![D_79]: (r2_hidden(D_79, k1_tarski(D_79)))), inference(superposition, [status(thm), theory('equality')], [c_203, c_120])).
% 3.05/1.50  tff(c_60, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.05/1.50  tff(c_121, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_60])).
% 3.05/1.50  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.50  tff(c_125, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_121, c_6])).
% 3.05/1.50  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_125])).
% 3.05/1.50  tff(c_133, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 3.05/1.50  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.50  tff(c_134, plain, (~r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_60])).
% 3.05/1.50  tff(c_56, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.05/1.50  tff(c_248, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_134, c_56])).
% 3.05/1.50  tff(c_251, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6')) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_2, c_248])).
% 3.05/1.50  tff(c_254, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_251])).
% 3.05/1.50  tff(c_42, plain, (![A_22, B_23]: (r1_xboole_0(k1_tarski(A_22), k1_tarski(B_23)) | B_23=A_22)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.05/1.50  tff(c_136, plain, (![A_62, B_63, C_64]: (~r1_xboole_0(A_62, B_63) | ~r2_hidden(C_64, B_63) | ~r2_hidden(C_64, A_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.05/1.50  tff(c_139, plain, (![C_64, B_23, A_22]: (~r2_hidden(C_64, k1_tarski(B_23)) | ~r2_hidden(C_64, k1_tarski(A_22)) | B_23=A_22)), inference(resolution, [status(thm)], [c_42, c_136])).
% 3.05/1.50  tff(c_260, plain, (![A_82]: (~r2_hidden('#skF_4', k1_tarski(A_82)) | A_82='#skF_6')), inference(resolution, [status(thm)], [c_254, c_139])).
% 3.05/1.50  tff(c_267, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_212, c_260])).
% 3.05/1.50  tff(c_273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_267])).
% 3.05/1.50  tff(c_274, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_58])).
% 3.05/1.50  tff(c_285, plain, (![D_85, A_86, B_87]: (r2_hidden(D_85, A_86) | ~r2_hidden(D_85, k4_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.50  tff(c_288, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_274, c_285])).
% 3.05/1.50  tff(c_292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_288])).
% 3.05/1.50  tff(c_293, plain, ('#skF_6'!='#skF_4' | '#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 3.05/1.50  tff(c_295, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_293])).
% 3.05/1.50  tff(c_670, plain, (![A_165, B_166, C_167, D_168]: (k3_enumset1(A_165, A_165, B_166, C_167, D_168)=k2_enumset1(A_165, B_166, C_167, D_168))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.05/1.50  tff(c_686, plain, (![D_169]: (k2_enumset1(D_169, D_169, D_169, D_169)=k1_tarski(D_169))), inference(superposition, [status(thm), theory('equality')], [c_670, c_30])).
% 3.05/1.50  tff(c_702, plain, (![D_170]: (k2_tarski(D_170, D_170)=k1_tarski(D_170))), inference(superposition, [status(thm), theory('equality')], [c_686, c_28])).
% 3.05/1.50  tff(c_320, plain, (![A_103, C_104, B_105]: (r2_hidden(A_103, C_104) | ~r1_tarski(k2_tarski(A_103, B_105), C_104))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.05/1.50  tff(c_324, plain, (![B_20, C_21]: (r2_hidden(B_20, k2_tarski(B_20, C_21)))), inference(resolution, [status(thm)], [c_34, c_320])).
% 3.05/1.50  tff(c_711, plain, (![D_170]: (r2_hidden(D_170, k1_tarski(D_170)))), inference(superposition, [status(thm), theory('equality')], [c_702, c_324])).
% 3.05/1.50  tff(c_525, plain, (![A_141, B_142, C_143, D_144]: (k3_enumset1(A_141, A_141, B_142, C_143, D_144)=k2_enumset1(A_141, B_142, C_143, D_144))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.05/1.50  tff(c_541, plain, (![D_145]: (k2_enumset1(D_145, D_145, D_145, D_145)=k1_tarski(D_145))), inference(superposition, [status(thm), theory('equality')], [c_525, c_30])).
% 3.05/1.50  tff(c_557, plain, (![D_146]: (k2_tarski(D_146, D_146)=k1_tarski(D_146))), inference(superposition, [status(thm), theory('equality')], [c_541, c_28])).
% 3.05/1.50  tff(c_605, plain, (![D_151]: (r2_hidden(D_151, k1_tarski(D_151)))), inference(superposition, [status(thm), theory('equality')], [c_557, c_324])).
% 3.05/1.50  tff(c_386, plain, (![A_121, B_122, C_123, D_124]: (k3_enumset1(A_121, A_121, B_122, C_123, D_124)=k2_enumset1(A_121, B_122, C_123, D_124))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.05/1.50  tff(c_402, plain, (![D_125]: (k2_enumset1(D_125, D_125, D_125, D_125)=k1_tarski(D_125))), inference(superposition, [status(thm), theory('equality')], [c_386, c_30])).
% 3.05/1.50  tff(c_418, plain, (![D_126]: (k2_tarski(D_126, D_126)=k1_tarski(D_126))), inference(superposition, [status(thm), theory('equality')], [c_402, c_28])).
% 3.05/1.50  tff(c_424, plain, (![D_126]: (r2_hidden(D_126, k1_tarski(D_126)))), inference(superposition, [status(thm), theory('equality')], [c_418, c_324])).
% 3.05/1.50  tff(c_294, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_52])).
% 3.05/1.50  tff(c_54, plain, (r2_hidden('#skF_4', '#skF_5') | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.05/1.50  tff(c_333, plain, (r2_hidden('#skF_4', '#skF_5') | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_294, c_54])).
% 3.05/1.50  tff(c_334, plain, ('#skF_7'='#skF_9'), inference(splitLeft, [status(thm)], [c_333])).
% 3.05/1.50  tff(c_360, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_60])).
% 3.05/1.50  tff(c_361, plain, (r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_360])).
% 3.05/1.50  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.50  tff(c_368, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_361, c_4])).
% 3.05/1.50  tff(c_457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_424, c_368])).
% 3.05/1.50  tff(c_458, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_360])).
% 3.05/1.50  tff(c_477, plain, (![D_133, A_134, B_135]: (r2_hidden(D_133, k4_xboole_0(A_134, B_135)) | r2_hidden(D_133, B_135) | ~r2_hidden(D_133, A_134))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.50  tff(c_459, plain, (~r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_360])).
% 3.05/1.50  tff(c_475, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_56])).
% 3.05/1.50  tff(c_476, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_459, c_475])).
% 3.05/1.50  tff(c_480, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6')) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_477, c_476])).
% 3.05/1.50  tff(c_492, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_480])).
% 3.05/1.50  tff(c_460, plain, (![A_127, B_128, C_129]: (~r1_xboole_0(A_127, B_128) | ~r2_hidden(C_129, B_128) | ~r2_hidden(C_129, A_127))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.05/1.50  tff(c_463, plain, (![C_129, B_23, A_22]: (~r2_hidden(C_129, k1_tarski(B_23)) | ~r2_hidden(C_129, k1_tarski(A_22)) | B_23=A_22)), inference(resolution, [status(thm)], [c_42, c_460])).
% 3.05/1.50  tff(c_500, plain, (![A_22]: (~r2_hidden('#skF_4', k1_tarski(A_22)) | A_22='#skF_6')), inference(resolution, [status(thm)], [c_492, c_463])).
% 3.05/1.50  tff(c_613, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_605, c_500])).
% 3.05/1.50  tff(c_621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_613])).
% 3.05/1.50  tff(c_622, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_333])).
% 3.05/1.50  tff(c_746, plain, (![D_172, A_173, B_174]: (r2_hidden(D_172, k4_xboole_0(A_173, B_174)) | r2_hidden(D_172, B_174) | ~r2_hidden(D_172, A_173))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.50  tff(c_623, plain, ('#skF_7'!='#skF_9'), inference(splitRight, [status(thm)], [c_333])).
% 3.05/1.50  tff(c_50, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.05/1.50  tff(c_659, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_294, c_50])).
% 3.05/1.50  tff(c_660, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_623, c_659])).
% 3.05/1.50  tff(c_749, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6')) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_746, c_660])).
% 3.05/1.50  tff(c_758, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_749])).
% 3.05/1.50  tff(c_644, plain, (![A_156, B_157, C_158]: (~r1_xboole_0(A_156, B_157) | ~r2_hidden(C_158, B_157) | ~r2_hidden(C_158, A_156))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.05/1.50  tff(c_647, plain, (![C_158, B_23, A_22]: (~r2_hidden(C_158, k1_tarski(B_23)) | ~r2_hidden(C_158, k1_tarski(A_22)) | B_23=A_22)), inference(resolution, [status(thm)], [c_42, c_644])).
% 3.05/1.50  tff(c_770, plain, (![A_177]: (~r2_hidden('#skF_4', k1_tarski(A_177)) | A_177='#skF_6')), inference(resolution, [status(thm)], [c_758, c_647])).
% 3.05/1.50  tff(c_777, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_711, c_770])).
% 3.05/1.50  tff(c_783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_777])).
% 3.05/1.50  tff(c_784, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_293])).
% 3.05/1.50  tff(c_785, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_293])).
% 3.05/1.50  tff(c_816, plain, (r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_784, c_785, c_58])).
% 3.05/1.50  tff(c_844, plain, (![D_200, B_201, A_202]: (~r2_hidden(D_200, B_201) | ~r2_hidden(D_200, k4_xboole_0(A_202, B_201)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.50  tff(c_853, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_816, c_844])).
% 3.05/1.50  tff(c_961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_928, c_853])).
% 3.05/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.50  
% 3.05/1.50  Inference rules
% 3.05/1.50  ----------------------
% 3.05/1.50  #Ref     : 0
% 3.05/1.50  #Sup     : 198
% 3.05/1.50  #Fact    : 0
% 3.05/1.50  #Define  : 0
% 3.05/1.50  #Split   : 6
% 3.05/1.50  #Chain   : 0
% 3.05/1.50  #Close   : 0
% 3.05/1.50  
% 3.05/1.50  Ordering : KBO
% 3.05/1.50  
% 3.05/1.50  Simplification rules
% 3.05/1.50  ----------------------
% 3.05/1.50  #Subsume      : 5
% 3.05/1.50  #Demod        : 52
% 3.05/1.50  #Tautology    : 92
% 3.05/1.50  #SimpNegUnit  : 8
% 3.05/1.50  #BackRed      : 4
% 3.05/1.50  
% 3.05/1.50  #Partial instantiations: 0
% 3.05/1.50  #Strategies tried      : 1
% 3.05/1.50  
% 3.05/1.50  Timing (in seconds)
% 3.05/1.50  ----------------------
% 3.05/1.51  Preprocessing        : 0.34
% 3.05/1.51  Parsing              : 0.17
% 3.05/1.51  CNF conversion       : 0.03
% 3.05/1.51  Main loop            : 0.40
% 3.05/1.51  Inferencing          : 0.15
% 3.05/1.51  Reduction            : 0.12
% 3.05/1.51  Demodulation         : 0.08
% 3.05/1.51  BG Simplification    : 0.02
% 3.05/1.51  Subsumption          : 0.06
% 3.05/1.51  Abstraction          : 0.02
% 3.05/1.51  MUC search           : 0.00
% 3.05/1.51  Cooper               : 0.00
% 3.05/1.51  Total                : 0.78
% 3.05/1.51  Index Insertion      : 0.00
% 3.05/1.51  Index Deletion       : 0.00
% 3.05/1.51  Index Matching       : 0.00
% 3.05/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
