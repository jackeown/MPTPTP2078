%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:41 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 680 expanded)
%              Number of leaves         :   33 ( 209 expanded)
%              Depth                    :   13
%              Number of atoms          :  197 (1347 expanded)
%              Number of equality atoms :  119 (1136 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_73,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_85,plain,(
    ! [A_75,B_76] :
      ( k2_xboole_0(k1_tarski(A_75),B_76) = B_76
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    ! [A_67,B_68] : k2_xboole_0(k1_tarski(A_67),B_68) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,(
    ! [A_75] : ~ r2_hidden(A_75,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_46])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_102,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_135,plain,(
    ! [E_91,F_92,A_93,B_94] :
      ( r2_hidden(k4_tarski(E_91,F_92),k2_zfmisc_1(A_93,B_94))
      | ~ r2_hidden(F_92,B_94)
      | ~ r2_hidden(E_91,A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_141,plain,(
    ! [E_91,F_92] :
      ( r2_hidden(k4_tarski(E_91,F_92),k1_xboole_0)
      | ~ r2_hidden(F_92,'#skF_11')
      | ~ r2_hidden(E_91,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_135])).

tff(c_143,plain,(
    ! [F_92,E_91] :
      ( ~ r2_hidden(F_92,'#skF_11')
      | ~ r2_hidden(E_91,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_141])).

tff(c_145,plain,(
    ! [E_95] : ~ r2_hidden(E_95,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_149,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_149])).

tff(c_155,plain,(
    ! [F_96] : ~ r2_hidden(F_96,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_159,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_4,c_155])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_159])).

tff(c_164,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_166,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_168,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_4])).

tff(c_24,plain,(
    ! [A_31,B_32,D_58] :
      ( r2_hidden('#skF_7'(A_31,B_32,k2_zfmisc_1(A_31,B_32),D_58),B_32)
      | ~ r2_hidden(D_58,k2_zfmisc_1(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_227,plain,(
    ! [A_122,B_123,D_124] :
      ( r2_hidden('#skF_6'(A_122,B_123,k2_zfmisc_1(A_122,B_123),D_124),A_122)
      | ~ r2_hidden(D_124,k2_zfmisc_1(A_122,B_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_90,plain,(
    ! [B_76,A_75] :
      ( k1_xboole_0 != B_76
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_46])).

tff(c_167,plain,(
    ! [B_76,A_75] :
      ( B_76 != '#skF_9'
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_90])).

tff(c_233,plain,(
    ! [A_125,D_126,B_127] :
      ( A_125 != '#skF_9'
      | ~ r2_hidden(D_126,k2_zfmisc_1(A_125,B_127)) ) ),
    inference(resolution,[status(thm)],[c_227,c_167])).

tff(c_249,plain,(
    ! [A_128,B_129] :
      ( A_128 != '#skF_9'
      | k2_zfmisc_1(A_128,B_129) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_168,c_233])).

tff(c_231,plain,(
    ! [A_122,D_124,B_123] :
      ( A_122 != '#skF_9'
      | ~ r2_hidden(D_124,k2_zfmisc_1(A_122,B_123)) ) ),
    inference(resolution,[status(thm)],[c_227,c_167])).

tff(c_255,plain,(
    ! [A_128,D_124] :
      ( A_128 != '#skF_9'
      | ~ r2_hidden(D_124,'#skF_9')
      | A_128 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_231])).

tff(c_279,plain,(
    ! [A_128] :
      ( A_128 != '#skF_9'
      | A_128 != '#skF_9' ) ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_285,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_279])).

tff(c_300,plain,(
    ! [D_133] : ~ r2_hidden(D_133,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_318,plain,(
    ! [D_134,A_135] : ~ r2_hidden(D_134,k2_zfmisc_1(A_135,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_24,c_300])).

tff(c_341,plain,(
    ! [A_135] : k2_zfmisc_1(A_135,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_168,c_318])).

tff(c_165,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_181,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_165])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_182,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_56])).

tff(c_183,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_182])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_183])).

tff(c_346,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_445,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_165])).

tff(c_350,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_4])).

tff(c_408,plain,(
    ! [A_157,B_158,D_159] :
      ( r2_hidden('#skF_6'(A_157,B_158,k2_zfmisc_1(A_157,B_158),D_159),A_157)
      | ~ r2_hidden(D_159,k2_zfmisc_1(A_157,B_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_349,plain,(
    ! [B_76,A_75] :
      ( B_76 != '#skF_8'
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_90])).

tff(c_414,plain,(
    ! [A_160,D_161,B_162] :
      ( A_160 != '#skF_8'
      | ~ r2_hidden(D_161,k2_zfmisc_1(A_160,B_162)) ) ),
    inference(resolution,[status(thm)],[c_408,c_349])).

tff(c_429,plain,(
    ! [B_162] : k2_zfmisc_1('#skF_8',B_162) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_350,c_414])).

tff(c_348,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_364,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_348])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_364])).

tff(c_433,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_456,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_433])).

tff(c_457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_456])).

tff(c_459,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_458,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_472,plain,
    ( '#skF_11' = '#skF_8'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_459,c_458])).

tff(c_473,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_476,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_459])).

tff(c_491,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_4])).

tff(c_561,plain,(
    ! [A_195,B_196,D_197] :
      ( r2_hidden('#skF_7'(A_195,B_196,k2_zfmisc_1(A_195,B_196),D_197),B_196)
      | ~ r2_hidden(D_197,k2_zfmisc_1(A_195,B_196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_506,plain,(
    ! [A_168,B_169] :
      ( k2_xboole_0(k1_tarski(A_168),B_169) = B_169
      | ~ r2_hidden(A_168,B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_461,plain,(
    ! [A_67,B_68] : k2_xboole_0(k1_tarski(A_67),B_68) != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_46])).

tff(c_489,plain,(
    ! [A_67,B_68] : k2_xboole_0(k1_tarski(A_67),B_68) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_461])).

tff(c_511,plain,(
    ! [B_169,A_168] :
      ( B_169 != '#skF_9'
      | ~ r2_hidden(A_168,B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_489])).

tff(c_618,plain,(
    ! [B_203,D_204,A_205] :
      ( B_203 != '#skF_9'
      | ~ r2_hidden(D_204,k2_zfmisc_1(A_205,B_203)) ) ),
    inference(resolution,[status(thm)],[c_561,c_511])).

tff(c_641,plain,(
    ! [A_205] : k2_zfmisc_1(A_205,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_491,c_618])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_494,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_473,c_476,c_48])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_494])).

tff(c_645,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_649,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_459])).

tff(c_677,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_4])).

tff(c_741,plain,(
    ! [A_235,B_236,D_237] :
      ( r2_hidden('#skF_6'(A_235,B_236,k2_zfmisc_1(A_235,B_236),D_237),A_235)
      | ~ r2_hidden(D_237,k2_zfmisc_1(A_235,B_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_688,plain,(
    ! [A_211,B_212] :
      ( k2_xboole_0(k1_tarski(A_211),B_212) = B_212
      | ~ r2_hidden(A_211,B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_675,plain,(
    ! [A_67,B_68] : k2_xboole_0(k1_tarski(A_67),B_68) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_461])).

tff(c_693,plain,(
    ! [B_212,A_211] :
      ( B_212 != '#skF_8'
      | ~ r2_hidden(A_211,B_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_675])).

tff(c_747,plain,(
    ! [A_238,D_239,B_240] :
      ( A_238 != '#skF_8'
      | ~ r2_hidden(D_239,k2_zfmisc_1(A_238,B_240)) ) ),
    inference(resolution,[status(thm)],[c_741,c_693])).

tff(c_772,plain,(
    ! [B_240] : k2_zfmisc_1('#skF_8',B_240) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_677,c_747])).

tff(c_659,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_48])).

tff(c_660,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_659])).

tff(c_666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_660])).

tff(c_667,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_674,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_667])).

tff(c_775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_674])).

tff(c_777,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_796,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_777,c_777,c_54])).

tff(c_797,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_796])).

tff(c_793,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_4])).

tff(c_798,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_793])).

tff(c_879,plain,(
    ! [A_276,B_277,D_278] :
      ( r2_hidden('#skF_6'(A_276,B_277,k2_zfmisc_1(A_276,B_277),D_278),A_276)
      | ~ r2_hidden(D_278,k2_zfmisc_1(A_276,B_277)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_827,plain,(
    ! [A_252,B_253] :
      ( k2_xboole_0(k1_tarski(A_252),B_253) = B_253
      | ~ r2_hidden(A_252,B_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_778,plain,(
    ! [A_67,B_68] : k2_xboole_0(k1_tarski(A_67),B_68) != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_46])).

tff(c_800,plain,(
    ! [A_67,B_68] : k2_xboole_0(k1_tarski(A_67),B_68) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_778])).

tff(c_832,plain,(
    ! [B_253,A_252] :
      ( B_253 != '#skF_8'
      | ~ r2_hidden(A_252,B_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_800])).

tff(c_885,plain,(
    ! [A_279,D_280,B_281] :
      ( A_279 != '#skF_8'
      | ~ r2_hidden(D_280,k2_zfmisc_1(A_279,B_281)) ) ),
    inference(resolution,[status(thm)],[c_879,c_832])).

tff(c_910,plain,(
    ! [B_281] : k2_zfmisc_1('#skF_8',B_281) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_798,c_885])).

tff(c_776,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_788,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_776])).

tff(c_801,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_788])).

tff(c_913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_801])).

tff(c_914,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_916,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_793])).

tff(c_1068,plain,(
    ! [A_323,B_324,D_325] :
      ( r2_hidden('#skF_7'(A_323,B_324,k2_zfmisc_1(A_323,B_324),D_325),B_324)
      | ~ r2_hidden(D_325,k2_zfmisc_1(A_323,B_324)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_999,plain,(
    ! [A_314,B_315,D_316] :
      ( r2_hidden('#skF_6'(A_314,B_315,k2_zfmisc_1(A_314,B_315),D_316),A_314)
      | ~ r2_hidden(D_316,k2_zfmisc_1(A_314,B_315)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_949,plain,(
    ! [A_290,B_291] :
      ( k2_xboole_0(k1_tarski(A_290),B_291) = B_291
      | ~ r2_hidden(A_290,B_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_918,plain,(
    ! [A_67,B_68] : k2_xboole_0(k1_tarski(A_67),B_68) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_778])).

tff(c_954,plain,(
    ! [B_291,A_290] :
      ( B_291 != '#skF_9'
      | ~ r2_hidden(A_290,B_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_918])).

tff(c_1005,plain,(
    ! [A_317,D_318,B_319] :
      ( A_317 != '#skF_9'
      | ~ r2_hidden(D_318,k2_zfmisc_1(A_317,B_319)) ) ),
    inference(resolution,[status(thm)],[c_999,c_954])).

tff(c_1021,plain,(
    ! [A_320,B_321] :
      ( A_320 != '#skF_9'
      | k2_zfmisc_1(A_320,B_321) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_916,c_1005])).

tff(c_1003,plain,(
    ! [A_314,D_316,B_315] :
      ( A_314 != '#skF_9'
      | ~ r2_hidden(D_316,k2_zfmisc_1(A_314,B_315)) ) ),
    inference(resolution,[status(thm)],[c_999,c_954])).

tff(c_1027,plain,(
    ! [A_320,D_316] :
      ( A_320 != '#skF_9'
      | ~ r2_hidden(D_316,'#skF_9')
      | A_320 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_1003])).

tff(c_1047,plain,(
    ! [A_320] :
      ( A_320 != '#skF_9'
      | A_320 != '#skF_9' ) ),
    inference(splitLeft,[status(thm)],[c_1027])).

tff(c_1053,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1047])).

tff(c_1054,plain,(
    ! [D_316] : ~ r2_hidden(D_316,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1027])).

tff(c_1086,plain,(
    ! [D_326,A_327] : ~ r2_hidden(D_326,k2_zfmisc_1(A_327,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_1068,c_1054])).

tff(c_1109,plain,(
    ! [A_327] : k2_zfmisc_1(A_327,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_916,c_1086])).

tff(c_919,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_788])).

tff(c_1113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_919])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:04:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.39  
% 2.87/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.39  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 2.87/1.39  
% 2.87/1.39  %Foreground sorts:
% 2.87/1.39  
% 2.87/1.39  
% 2.87/1.39  %Background operators:
% 2.87/1.39  
% 2.87/1.39  
% 2.87/1.39  %Foreground operators:
% 2.87/1.39  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.87/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.39  tff('#skF_11', type, '#skF_11': $i).
% 2.87/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.87/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.87/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.87/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.39  tff('#skF_10', type, '#skF_10': $i).
% 2.87/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.87/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.87/1.39  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.87/1.39  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.87/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.39  tff('#skF_9', type, '#skF_9': $i).
% 2.87/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.87/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.87/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.39  
% 2.87/1.42  tff(f_74, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.87/1.42  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.87/1.42  tff(f_64, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.87/1.42  tff(f_67, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.87/1.42  tff(f_60, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.87/1.42  tff(c_50, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.42  tff(c_74, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_50])).
% 2.87/1.42  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.87/1.42  tff(c_52, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.42  tff(c_73, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_52])).
% 2.87/1.42  tff(c_85, plain, (![A_75, B_76]: (k2_xboole_0(k1_tarski(A_75), B_76)=B_76 | ~r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.42  tff(c_46, plain, (![A_67, B_68]: (k2_xboole_0(k1_tarski(A_67), B_68)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.42  tff(c_96, plain, (![A_75]: (~r2_hidden(A_75, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_85, c_46])).
% 2.87/1.42  tff(c_58, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.42  tff(c_102, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 2.87/1.42  tff(c_135, plain, (![E_91, F_92, A_93, B_94]: (r2_hidden(k4_tarski(E_91, F_92), k2_zfmisc_1(A_93, B_94)) | ~r2_hidden(F_92, B_94) | ~r2_hidden(E_91, A_93))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.42  tff(c_141, plain, (![E_91, F_92]: (r2_hidden(k4_tarski(E_91, F_92), k1_xboole_0) | ~r2_hidden(F_92, '#skF_11') | ~r2_hidden(E_91, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_135])).
% 2.87/1.42  tff(c_143, plain, (![F_92, E_91]: (~r2_hidden(F_92, '#skF_11') | ~r2_hidden(E_91, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_96, c_141])).
% 2.87/1.42  tff(c_145, plain, (![E_95]: (~r2_hidden(E_95, '#skF_10'))), inference(splitLeft, [status(thm)], [c_143])).
% 2.87/1.42  tff(c_149, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_4, c_145])).
% 2.87/1.42  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_149])).
% 2.87/1.42  tff(c_155, plain, (![F_96]: (~r2_hidden(F_96, '#skF_11'))), inference(splitRight, [status(thm)], [c_143])).
% 2.87/1.42  tff(c_159, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_4, c_155])).
% 2.87/1.42  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_159])).
% 2.87/1.42  tff(c_164, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_58])).
% 2.87/1.42  tff(c_166, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_164])).
% 2.87/1.42  tff(c_168, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_4])).
% 2.87/1.42  tff(c_24, plain, (![A_31, B_32, D_58]: (r2_hidden('#skF_7'(A_31, B_32, k2_zfmisc_1(A_31, B_32), D_58), B_32) | ~r2_hidden(D_58, k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.42  tff(c_227, plain, (![A_122, B_123, D_124]: (r2_hidden('#skF_6'(A_122, B_123, k2_zfmisc_1(A_122, B_123), D_124), A_122) | ~r2_hidden(D_124, k2_zfmisc_1(A_122, B_123)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.42  tff(c_90, plain, (![B_76, A_75]: (k1_xboole_0!=B_76 | ~r2_hidden(A_75, B_76))), inference(superposition, [status(thm), theory('equality')], [c_85, c_46])).
% 2.87/1.42  tff(c_167, plain, (![B_76, A_75]: (B_76!='#skF_9' | ~r2_hidden(A_75, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_90])).
% 2.87/1.42  tff(c_233, plain, (![A_125, D_126, B_127]: (A_125!='#skF_9' | ~r2_hidden(D_126, k2_zfmisc_1(A_125, B_127)))), inference(resolution, [status(thm)], [c_227, c_167])).
% 2.87/1.42  tff(c_249, plain, (![A_128, B_129]: (A_128!='#skF_9' | k2_zfmisc_1(A_128, B_129)='#skF_9')), inference(resolution, [status(thm)], [c_168, c_233])).
% 2.87/1.42  tff(c_231, plain, (![A_122, D_124, B_123]: (A_122!='#skF_9' | ~r2_hidden(D_124, k2_zfmisc_1(A_122, B_123)))), inference(resolution, [status(thm)], [c_227, c_167])).
% 2.87/1.42  tff(c_255, plain, (![A_128, D_124]: (A_128!='#skF_9' | ~r2_hidden(D_124, '#skF_9') | A_128!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_249, c_231])).
% 2.87/1.42  tff(c_279, plain, (![A_128]: (A_128!='#skF_9' | A_128!='#skF_9')), inference(splitLeft, [status(thm)], [c_255])).
% 2.87/1.42  tff(c_285, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_279])).
% 2.87/1.42  tff(c_300, plain, (![D_133]: (~r2_hidden(D_133, '#skF_9'))), inference(splitRight, [status(thm)], [c_255])).
% 2.87/1.42  tff(c_318, plain, (![D_134, A_135]: (~r2_hidden(D_134, k2_zfmisc_1(A_135, '#skF_9')))), inference(resolution, [status(thm)], [c_24, c_300])).
% 2.87/1.42  tff(c_341, plain, (![A_135]: (k2_zfmisc_1(A_135, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_168, c_318])).
% 2.87/1.42  tff(c_165, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 2.87/1.42  tff(c_181, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_165])).
% 2.87/1.42  tff(c_56, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.42  tff(c_182, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_56])).
% 2.87/1.42  tff(c_183, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_181, c_182])).
% 2.87/1.42  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_341, c_183])).
% 2.87/1.42  tff(c_346, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_164])).
% 2.87/1.42  tff(c_445, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_346, c_165])).
% 2.87/1.42  tff(c_350, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_4])).
% 2.87/1.42  tff(c_408, plain, (![A_157, B_158, D_159]: (r2_hidden('#skF_6'(A_157, B_158, k2_zfmisc_1(A_157, B_158), D_159), A_157) | ~r2_hidden(D_159, k2_zfmisc_1(A_157, B_158)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.42  tff(c_349, plain, (![B_76, A_75]: (B_76!='#skF_8' | ~r2_hidden(A_75, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_90])).
% 2.87/1.42  tff(c_414, plain, (![A_160, D_161, B_162]: (A_160!='#skF_8' | ~r2_hidden(D_161, k2_zfmisc_1(A_160, B_162)))), inference(resolution, [status(thm)], [c_408, c_349])).
% 2.87/1.42  tff(c_429, plain, (![B_162]: (k2_zfmisc_1('#skF_8', B_162)='#skF_8')), inference(resolution, [status(thm)], [c_350, c_414])).
% 2.87/1.42  tff(c_348, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 2.87/1.42  tff(c_364, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_346, c_348])).
% 2.87/1.42  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_429, c_364])).
% 2.87/1.42  tff(c_433, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 2.87/1.42  tff(c_456, plain, (k2_zfmisc_1('#skF_10', '#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_346, c_433])).
% 2.87/1.42  tff(c_457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_445, c_456])).
% 2.87/1.42  tff(c_459, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_50])).
% 2.87/1.42  tff(c_458, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_50])).
% 2.87/1.42  tff(c_472, plain, ('#skF_11'='#skF_8' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_459, c_459, c_458])).
% 2.87/1.42  tff(c_473, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_472])).
% 2.87/1.42  tff(c_476, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_473, c_459])).
% 2.87/1.42  tff(c_491, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_476, c_4])).
% 2.87/1.42  tff(c_561, plain, (![A_195, B_196, D_197]: (r2_hidden('#skF_7'(A_195, B_196, k2_zfmisc_1(A_195, B_196), D_197), B_196) | ~r2_hidden(D_197, k2_zfmisc_1(A_195, B_196)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.42  tff(c_506, plain, (![A_168, B_169]: (k2_xboole_0(k1_tarski(A_168), B_169)=B_169 | ~r2_hidden(A_168, B_169))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.42  tff(c_461, plain, (![A_67, B_68]: (k2_xboole_0(k1_tarski(A_67), B_68)!='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_46])).
% 2.87/1.42  tff(c_489, plain, (![A_67, B_68]: (k2_xboole_0(k1_tarski(A_67), B_68)!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_461])).
% 2.87/1.42  tff(c_511, plain, (![B_169, A_168]: (B_169!='#skF_9' | ~r2_hidden(A_168, B_169))), inference(superposition, [status(thm), theory('equality')], [c_506, c_489])).
% 2.87/1.42  tff(c_618, plain, (![B_203, D_204, A_205]: (B_203!='#skF_9' | ~r2_hidden(D_204, k2_zfmisc_1(A_205, B_203)))), inference(resolution, [status(thm)], [c_561, c_511])).
% 2.87/1.42  tff(c_641, plain, (![A_205]: (k2_zfmisc_1(A_205, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_491, c_618])).
% 2.87/1.42  tff(c_48, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.42  tff(c_494, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_476, c_473, c_476, c_48])).
% 2.87/1.42  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_641, c_494])).
% 2.87/1.42  tff(c_645, plain, ('#skF_11'='#skF_8'), inference(splitRight, [status(thm)], [c_472])).
% 2.87/1.42  tff(c_649, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_645, c_459])).
% 2.87/1.42  tff(c_677, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_649, c_4])).
% 2.87/1.42  tff(c_741, plain, (![A_235, B_236, D_237]: (r2_hidden('#skF_6'(A_235, B_236, k2_zfmisc_1(A_235, B_236), D_237), A_235) | ~r2_hidden(D_237, k2_zfmisc_1(A_235, B_236)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.42  tff(c_688, plain, (![A_211, B_212]: (k2_xboole_0(k1_tarski(A_211), B_212)=B_212 | ~r2_hidden(A_211, B_212))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.42  tff(c_675, plain, (![A_67, B_68]: (k2_xboole_0(k1_tarski(A_67), B_68)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_645, c_461])).
% 2.87/1.42  tff(c_693, plain, (![B_212, A_211]: (B_212!='#skF_8' | ~r2_hidden(A_211, B_212))), inference(superposition, [status(thm), theory('equality')], [c_688, c_675])).
% 2.87/1.42  tff(c_747, plain, (![A_238, D_239, B_240]: (A_238!='#skF_8' | ~r2_hidden(D_239, k2_zfmisc_1(A_238, B_240)))), inference(resolution, [status(thm)], [c_741, c_693])).
% 2.87/1.42  tff(c_772, plain, (![B_240]: (k2_zfmisc_1('#skF_8', B_240)='#skF_8')), inference(resolution, [status(thm)], [c_677, c_747])).
% 2.87/1.42  tff(c_659, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_645, c_48])).
% 2.87/1.42  tff(c_660, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_659])).
% 2.87/1.42  tff(c_666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_649, c_660])).
% 2.87/1.42  tff(c_667, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_659])).
% 2.87/1.42  tff(c_674, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_649, c_667])).
% 2.87/1.42  tff(c_775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_772, c_674])).
% 2.87/1.42  tff(c_777, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_52])).
% 2.87/1.42  tff(c_54, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.42  tff(c_796, plain, ('#skF_10'='#skF_9' | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_777, c_777, c_777, c_54])).
% 2.87/1.42  tff(c_797, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_796])).
% 2.87/1.42  tff(c_793, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_777, c_4])).
% 2.87/1.42  tff(c_798, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_797, c_793])).
% 2.87/1.42  tff(c_879, plain, (![A_276, B_277, D_278]: (r2_hidden('#skF_6'(A_276, B_277, k2_zfmisc_1(A_276, B_277), D_278), A_276) | ~r2_hidden(D_278, k2_zfmisc_1(A_276, B_277)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.42  tff(c_827, plain, (![A_252, B_253]: (k2_xboole_0(k1_tarski(A_252), B_253)=B_253 | ~r2_hidden(A_252, B_253))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.42  tff(c_778, plain, (![A_67, B_68]: (k2_xboole_0(k1_tarski(A_67), B_68)!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_777, c_46])).
% 2.87/1.42  tff(c_800, plain, (![A_67, B_68]: (k2_xboole_0(k1_tarski(A_67), B_68)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_797, c_778])).
% 2.87/1.42  tff(c_832, plain, (![B_253, A_252]: (B_253!='#skF_8' | ~r2_hidden(A_252, B_253))), inference(superposition, [status(thm), theory('equality')], [c_827, c_800])).
% 2.87/1.42  tff(c_885, plain, (![A_279, D_280, B_281]: (A_279!='#skF_8' | ~r2_hidden(D_280, k2_zfmisc_1(A_279, B_281)))), inference(resolution, [status(thm)], [c_879, c_832])).
% 2.87/1.42  tff(c_910, plain, (![B_281]: (k2_zfmisc_1('#skF_8', B_281)='#skF_8')), inference(resolution, [status(thm)], [c_798, c_885])).
% 2.87/1.42  tff(c_776, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 2.87/1.42  tff(c_788, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_777, c_776])).
% 2.87/1.42  tff(c_801, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_797, c_788])).
% 2.87/1.42  tff(c_913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_910, c_801])).
% 2.87/1.42  tff(c_914, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_796])).
% 2.87/1.42  tff(c_916, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_914, c_793])).
% 2.87/1.42  tff(c_1068, plain, (![A_323, B_324, D_325]: (r2_hidden('#skF_7'(A_323, B_324, k2_zfmisc_1(A_323, B_324), D_325), B_324) | ~r2_hidden(D_325, k2_zfmisc_1(A_323, B_324)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.42  tff(c_999, plain, (![A_314, B_315, D_316]: (r2_hidden('#skF_6'(A_314, B_315, k2_zfmisc_1(A_314, B_315), D_316), A_314) | ~r2_hidden(D_316, k2_zfmisc_1(A_314, B_315)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.42  tff(c_949, plain, (![A_290, B_291]: (k2_xboole_0(k1_tarski(A_290), B_291)=B_291 | ~r2_hidden(A_290, B_291))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.42  tff(c_918, plain, (![A_67, B_68]: (k2_xboole_0(k1_tarski(A_67), B_68)!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_914, c_778])).
% 2.87/1.42  tff(c_954, plain, (![B_291, A_290]: (B_291!='#skF_9' | ~r2_hidden(A_290, B_291))), inference(superposition, [status(thm), theory('equality')], [c_949, c_918])).
% 2.87/1.42  tff(c_1005, plain, (![A_317, D_318, B_319]: (A_317!='#skF_9' | ~r2_hidden(D_318, k2_zfmisc_1(A_317, B_319)))), inference(resolution, [status(thm)], [c_999, c_954])).
% 2.87/1.42  tff(c_1021, plain, (![A_320, B_321]: (A_320!='#skF_9' | k2_zfmisc_1(A_320, B_321)='#skF_9')), inference(resolution, [status(thm)], [c_916, c_1005])).
% 2.87/1.42  tff(c_1003, plain, (![A_314, D_316, B_315]: (A_314!='#skF_9' | ~r2_hidden(D_316, k2_zfmisc_1(A_314, B_315)))), inference(resolution, [status(thm)], [c_999, c_954])).
% 2.87/1.42  tff(c_1027, plain, (![A_320, D_316]: (A_320!='#skF_9' | ~r2_hidden(D_316, '#skF_9') | A_320!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1021, c_1003])).
% 2.87/1.42  tff(c_1047, plain, (![A_320]: (A_320!='#skF_9' | A_320!='#skF_9')), inference(splitLeft, [status(thm)], [c_1027])).
% 2.87/1.42  tff(c_1053, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_1047])).
% 2.87/1.42  tff(c_1054, plain, (![D_316]: (~r2_hidden(D_316, '#skF_9'))), inference(splitRight, [status(thm)], [c_1027])).
% 2.87/1.42  tff(c_1086, plain, (![D_326, A_327]: (~r2_hidden(D_326, k2_zfmisc_1(A_327, '#skF_9')))), inference(resolution, [status(thm)], [c_1068, c_1054])).
% 2.87/1.42  tff(c_1109, plain, (![A_327]: (k2_zfmisc_1(A_327, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_916, c_1086])).
% 2.87/1.42  tff(c_919, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_914, c_788])).
% 2.87/1.42  tff(c_1113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1109, c_919])).
% 2.87/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.42  
% 2.87/1.42  Inference rules
% 2.87/1.42  ----------------------
% 2.87/1.42  #Ref     : 2
% 2.87/1.42  #Sup     : 220
% 2.87/1.42  #Fact    : 0
% 2.87/1.42  #Define  : 0
% 2.87/1.42  #Split   : 12
% 2.87/1.42  #Chain   : 0
% 2.87/1.42  #Close   : 0
% 2.87/1.42  
% 2.87/1.42  Ordering : KBO
% 2.87/1.42  
% 2.87/1.42  Simplification rules
% 2.87/1.42  ----------------------
% 2.87/1.42  #Subsume      : 39
% 2.87/1.42  #Demod        : 118
% 2.87/1.42  #Tautology    : 137
% 2.87/1.42  #SimpNegUnit  : 10
% 2.87/1.42  #BackRed      : 49
% 2.87/1.42  
% 2.87/1.42  #Partial instantiations: 0
% 2.87/1.42  #Strategies tried      : 1
% 2.87/1.42  
% 2.87/1.42  Timing (in seconds)
% 2.87/1.42  ----------------------
% 2.87/1.42  Preprocessing        : 0.34
% 2.87/1.42  Parsing              : 0.17
% 2.87/1.42  CNF conversion       : 0.02
% 2.87/1.42  Main loop            : 0.35
% 2.87/1.42  Inferencing          : 0.14
% 2.87/1.42  Reduction            : 0.09
% 2.87/1.42  Demodulation         : 0.06
% 2.87/1.42  BG Simplification    : 0.02
% 2.87/1.42  Subsumption          : 0.05
% 2.87/1.42  Abstraction          : 0.02
% 2.87/1.42  MUC search           : 0.00
% 2.87/1.42  Cooper               : 0.00
% 2.87/1.42  Total                : 0.74
% 2.87/1.42  Index Insertion      : 0.00
% 2.87/1.42  Index Deletion       : 0.00
% 2.87/1.42  Index Matching       : 0.00
% 2.87/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
