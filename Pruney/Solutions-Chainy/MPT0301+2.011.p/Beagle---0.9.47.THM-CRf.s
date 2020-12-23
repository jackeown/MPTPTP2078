%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:41 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 567 expanded)
%              Number of leaves         :   26 ( 173 expanded)
%              Depth                    :   13
%              Number of atoms          :  201 (1133 expanded)
%              Number of equality atoms :   89 ( 858 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_40,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_59,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_86,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( r2_hidden(k4_tarski(A_62,B_63),k2_zfmisc_1(C_64,D_65))
      | ~ r2_hidden(B_63,D_65)
      | ~ r2_hidden(A_62,C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(k4_tarski(A_66,B_67),k1_xboole_0)
      | ~ r2_hidden(B_67,'#skF_12')
      | ~ r2_hidden(A_66,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_86])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [B_67,A_66] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(B_67,'#skF_12')
      | ~ r2_hidden(A_66,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_116,plain,(
    ! [B_67,A_66] :
      ( ~ r2_hidden(B_67,'#skF_12')
      | ~ r2_hidden(A_66,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_111])).

tff(c_119,plain,(
    ! [A_68] : ~ r2_hidden(A_68,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_123,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_8,c_119])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_123])).

tff(c_134,plain,(
    ! [B_69] : ~ r2_hidden(B_69,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_138,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_138])).

tff(c_147,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_149,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_152,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_6])).

tff(c_160,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_8])).

tff(c_187,plain,(
    ! [A_84,B_85,D_86] :
      ( r2_hidden('#skF_8'(A_84,B_85,k2_zfmisc_1(A_84,B_85),D_86),B_85)
      | ~ r2_hidden(D_86,k2_zfmisc_1(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_192,plain,(
    ! [B_87,D_88,A_89] :
      ( ~ v1_xboole_0(B_87)
      | ~ r2_hidden(D_88,k2_zfmisc_1(A_89,B_87)) ) ),
    inference(resolution,[status(thm)],[c_187,c_2])).

tff(c_217,plain,(
    ! [B_92,A_93] :
      ( ~ v1_xboole_0(B_92)
      | k2_zfmisc_1(A_93,B_92) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_160,c_192])).

tff(c_223,plain,(
    ! [A_93] : k2_zfmisc_1(A_93,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_152,c_217])).

tff(c_148,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_157,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_148])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_158,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10'
    | k2_zfmisc_1('#skF_11','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_149,c_48])).

tff(c_159,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_158])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_159])).

tff(c_237,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_248,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_8])).

tff(c_16,plain,(
    ! [A_7,B_8,D_34] :
      ( r2_hidden('#skF_7'(A_7,B_8,k2_zfmisc_1(A_7,B_8),D_34),A_7)
      | ~ r2_hidden(D_34,k2_zfmisc_1(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_241,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_6])).

tff(c_278,plain,(
    ! [A_115,B_116,D_117] :
      ( r2_hidden('#skF_8'(A_115,B_116,k2_zfmisc_1(A_115,B_116),D_117),B_116)
      | ~ r2_hidden(D_117,k2_zfmisc_1(A_115,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_288,plain,(
    ! [B_121,D_122,A_123] :
      ( ~ v1_xboole_0(B_121)
      | ~ r2_hidden(D_122,k2_zfmisc_1(A_123,B_121)) ) ),
    inference(resolution,[status(thm)],[c_278,c_2])).

tff(c_321,plain,(
    ! [B_126,A_127] :
      ( ~ v1_xboole_0(B_126)
      | k2_zfmisc_1(A_127,B_126) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_248,c_288])).

tff(c_347,plain,(
    ! [A_131] : k2_zfmisc_1(A_131,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_241,c_321])).

tff(c_282,plain,(
    ! [B_116,D_117,A_115] :
      ( ~ v1_xboole_0(B_116)
      | ~ r2_hidden(D_117,k2_zfmisc_1(A_115,B_116)) ) ),
    inference(resolution,[status(thm)],[c_278,c_2])).

tff(c_355,plain,(
    ! [D_117] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ r2_hidden(D_117,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_282])).

tff(c_385,plain,(
    ! [D_132] : ~ r2_hidden(D_132,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_355])).

tff(c_416,plain,(
    ! [D_133,B_134] : ~ r2_hidden(D_133,k2_zfmisc_1('#skF_9',B_134)) ),
    inference(resolution,[status(thm)],[c_16,c_385])).

tff(c_453,plain,(
    ! [B_134] : k2_zfmisc_1('#skF_9',B_134) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_248,c_416])).

tff(c_247,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_148])).

tff(c_260,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_237,c_48])).

tff(c_261,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_260])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_261])).

tff(c_460,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_462,plain,(
    v1_xboole_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_6])).

tff(c_679,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_8])).

tff(c_710,plain,(
    ! [A_206,B_207,D_208] :
      ( r2_hidden('#skF_8'(A_206,B_207,k2_zfmisc_1(A_206,B_207),D_208),B_207)
      | ~ r2_hidden(D_208,k2_zfmisc_1(A_206,B_207)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_715,plain,(
    ! [B_209,D_210,A_211] :
      ( ~ v1_xboole_0(B_209)
      | ~ r2_hidden(D_210,k2_zfmisc_1(A_211,B_209)) ) ),
    inference(resolution,[status(thm)],[c_710,c_2])).

tff(c_743,plain,(
    ! [B_214,A_215] :
      ( ~ v1_xboole_0(B_214)
      | k2_zfmisc_1(A_215,B_214) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_679,c_715])).

tff(c_749,plain,(
    ! [A_215] : k2_zfmisc_1(A_215,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_462,c_743])).

tff(c_605,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_8])).

tff(c_632,plain,(
    ! [A_178,B_179,D_180] :
      ( r2_hidden('#skF_8'(A_178,B_179,k2_zfmisc_1(A_178,B_179),D_180),B_179)
      | ~ r2_hidden(D_180,k2_zfmisc_1(A_178,B_179)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_637,plain,(
    ! [B_181,D_182,A_183] :
      ( ~ v1_xboole_0(B_181)
      | ~ r2_hidden(D_182,k2_zfmisc_1(A_183,B_181)) ) ),
    inference(resolution,[status(thm)],[c_632,c_2])).

tff(c_662,plain,(
    ! [B_186,A_187] :
      ( ~ v1_xboole_0(B_186)
      | k2_zfmisc_1(A_187,B_186) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_605,c_637])).

tff(c_668,plain,(
    ! [A_187] : k2_zfmisc_1(A_187,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_462,c_662])).

tff(c_482,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_8])).

tff(c_556,plain,(
    ! [A_159,B_160,D_161] :
      ( r2_hidden('#skF_7'(A_159,B_160,k2_zfmisc_1(A_159,B_160),D_161),A_159)
      | ~ r2_hidden(D_161,k2_zfmisc_1(A_159,B_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_461,plain,(
    '#skF_11' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_57])).

tff(c_471,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_9' = '#skF_12'
    | k2_zfmisc_1('#skF_11','#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_460,c_460,c_50])).

tff(c_472,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_505,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( r2_hidden(k4_tarski(A_149,B_150),k2_zfmisc_1(C_151,D_152))
      | ~ r2_hidden(B_150,D_152)
      | ~ r2_hidden(A_149,C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_521,plain,(
    ! [C_153,D_154,B_155,A_156] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_153,D_154))
      | ~ r2_hidden(B_155,D_154)
      | ~ r2_hidden(A_156,C_153) ) ),
    inference(resolution,[status(thm)],[c_505,c_2])).

tff(c_523,plain,(
    ! [B_155,A_156] :
      ( ~ v1_xboole_0('#skF_12')
      | ~ r2_hidden(B_155,'#skF_12')
      | ~ r2_hidden(A_156,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_521])).

tff(c_525,plain,(
    ! [B_155,A_156] :
      ( ~ r2_hidden(B_155,'#skF_12')
      | ~ r2_hidden(A_156,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_523])).

tff(c_528,plain,(
    ! [A_157] : ~ r2_hidden(A_157,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_525])).

tff(c_532,plain,(
    '#skF_11' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_482,c_528])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_532])).

tff(c_541,plain,(
    ! [B_155] : ~ r2_hidden(B_155,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_570,plain,(
    ! [D_162,B_163] : ~ r2_hidden(D_162,k2_zfmisc_1('#skF_12',B_163)) ),
    inference(resolution,[status(thm)],[c_556,c_541])).

tff(c_589,plain,(
    ! [B_163] : k2_zfmisc_1('#skF_12',B_163) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_482,c_570])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_469,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_9' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_460,c_460,c_42])).

tff(c_470,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_459,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_467,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_459])).

tff(c_473,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_467])).

tff(c_594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_473])).

tff(c_596,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_596])).

tff(c_672,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_674,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_467])).

tff(c_762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_674])).

tff(c_764,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_763,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_770,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_764,c_763])).

tff(c_771,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_770])).

tff(c_765,plain,(
    v1_xboole_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_6])).

tff(c_772,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_765])).

tff(c_773,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_764])).

tff(c_785,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_8])).

tff(c_817,plain,(
    ! [A_237,B_238,D_239] :
      ( r2_hidden('#skF_8'(A_237,B_238,k2_zfmisc_1(A_237,B_238),D_239),B_238)
      | ~ r2_hidden(D_239,k2_zfmisc_1(A_237,B_238)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_822,plain,(
    ! [B_240,D_241,A_242] :
      ( ~ v1_xboole_0(B_240)
      | ~ r2_hidden(D_241,k2_zfmisc_1(A_242,B_240)) ) ),
    inference(resolution,[status(thm)],[c_817,c_2])).

tff(c_850,plain,(
    ! [B_245,A_246] :
      ( ~ v1_xboole_0(B_245)
      | k2_zfmisc_1(A_246,B_245) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_785,c_822])).

tff(c_856,plain,(
    ! [A_246] : k2_zfmisc_1(A_246,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_772,c_850])).

tff(c_44,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_798,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_771,c_773,c_44])).

tff(c_859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_798])).

tff(c_860,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_863,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_764])).

tff(c_877,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_8])).

tff(c_995,plain,(
    ! [A_273,B_274,D_275] :
      ( r2_hidden('#skF_7'(A_273,B_274,k2_zfmisc_1(A_273,B_274),D_275),A_273)
      | ~ r2_hidden(D_275,k2_zfmisc_1(A_273,B_274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_862,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_765])).

tff(c_909,plain,(
    ! [A_261,B_262,D_263] :
      ( r2_hidden('#skF_8'(A_261,B_262,k2_zfmisc_1(A_261,B_262),D_263),B_262)
      | ~ r2_hidden(D_263,k2_zfmisc_1(A_261,B_262)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_914,plain,(
    ! [B_264,D_265,A_266] :
      ( ~ v1_xboole_0(B_264)
      | ~ r2_hidden(D_265,k2_zfmisc_1(A_266,B_264)) ) ),
    inference(resolution,[status(thm)],[c_909,c_2])).

tff(c_934,plain,(
    ! [B_267,A_268] :
      ( ~ v1_xboole_0(B_267)
      | k2_zfmisc_1(A_268,B_267) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_877,c_914])).

tff(c_938,plain,(
    ! [A_269] : k2_zfmisc_1(A_269,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_862,c_934])).

tff(c_913,plain,(
    ! [B_262,D_263,A_261] :
      ( ~ v1_xboole_0(B_262)
      | ~ r2_hidden(D_263,k2_zfmisc_1(A_261,B_262)) ) ),
    inference(resolution,[status(thm)],[c_909,c_2])).

tff(c_943,plain,(
    ! [D_263] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ r2_hidden(D_263,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_938,c_913])).

tff(c_960,plain,(
    ! [D_263] : ~ r2_hidden(D_263,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_943])).

tff(c_1014,plain,(
    ! [D_276,B_277] : ~ r2_hidden(D_276,k2_zfmisc_1('#skF_9',B_277)) ),
    inference(resolution,[status(thm)],[c_995,c_960])).

tff(c_1041,plain,(
    ! [B_277] : k2_zfmisc_1('#skF_9',B_277) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_877,c_1014])).

tff(c_890,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_860,c_863,c_44])).

tff(c_1046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:15:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.50  
% 2.71/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.50  %$ r2_hidden > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_12
% 2.71/1.50  
% 2.71/1.50  %Foreground sorts:
% 2.71/1.50  
% 2.71/1.50  
% 2.71/1.50  %Background operators:
% 2.71/1.50  
% 2.71/1.50  
% 2.71/1.50  %Foreground operators:
% 2.71/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.71/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.50  tff('#skF_11', type, '#skF_11': $i).
% 2.71/1.50  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.71/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.71/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.71/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.71/1.50  tff('#skF_10', type, '#skF_10': $i).
% 2.71/1.50  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.71/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.71/1.50  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.71/1.50  tff('#skF_9', type, '#skF_9': $i).
% 2.71/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.71/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.50  tff('#skF_12', type, '#skF_12': $i).
% 2.71/1.50  
% 2.71/1.52  tff(f_65, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.71/1.52  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.71/1.52  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.71/1.52  tff(f_58, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.71/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.71/1.52  tff(f_52, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.71/1.52  tff(c_40, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.52  tff(c_58, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_40])).
% 2.71/1.52  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.71/1.52  tff(c_46, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.52  tff(c_57, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_46])).
% 2.71/1.52  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.52  tff(c_50, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.52  tff(c_59, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 2.71/1.52  tff(c_86, plain, (![A_62, B_63, C_64, D_65]: (r2_hidden(k4_tarski(A_62, B_63), k2_zfmisc_1(C_64, D_65)) | ~r2_hidden(B_63, D_65) | ~r2_hidden(A_62, C_64))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.52  tff(c_102, plain, (![A_66, B_67]: (r2_hidden(k4_tarski(A_66, B_67), k1_xboole_0) | ~r2_hidden(B_67, '#skF_12') | ~r2_hidden(A_66, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_86])).
% 2.71/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.52  tff(c_111, plain, (![B_67, A_66]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(B_67, '#skF_12') | ~r2_hidden(A_66, '#skF_11'))), inference(resolution, [status(thm)], [c_102, c_2])).
% 2.71/1.52  tff(c_116, plain, (![B_67, A_66]: (~r2_hidden(B_67, '#skF_12') | ~r2_hidden(A_66, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_111])).
% 2.71/1.52  tff(c_119, plain, (![A_68]: (~r2_hidden(A_68, '#skF_11'))), inference(splitLeft, [status(thm)], [c_116])).
% 2.71/1.52  tff(c_123, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_8, c_119])).
% 2.71/1.52  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_123])).
% 2.71/1.52  tff(c_134, plain, (![B_69]: (~r2_hidden(B_69, '#skF_12'))), inference(splitRight, [status(thm)], [c_116])).
% 2.71/1.52  tff(c_138, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_8, c_134])).
% 2.71/1.52  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_138])).
% 2.71/1.52  tff(c_147, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_50])).
% 2.71/1.52  tff(c_149, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_147])).
% 2.71/1.52  tff(c_152, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_6])).
% 2.71/1.52  tff(c_160, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_8])).
% 2.71/1.52  tff(c_187, plain, (![A_84, B_85, D_86]: (r2_hidden('#skF_8'(A_84, B_85, k2_zfmisc_1(A_84, B_85), D_86), B_85) | ~r2_hidden(D_86, k2_zfmisc_1(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.52  tff(c_192, plain, (![B_87, D_88, A_89]: (~v1_xboole_0(B_87) | ~r2_hidden(D_88, k2_zfmisc_1(A_89, B_87)))), inference(resolution, [status(thm)], [c_187, c_2])).
% 2.71/1.52  tff(c_217, plain, (![B_92, A_93]: (~v1_xboole_0(B_92) | k2_zfmisc_1(A_93, B_92)='#skF_10')), inference(resolution, [status(thm)], [c_160, c_192])).
% 2.71/1.52  tff(c_223, plain, (![A_93]: (k2_zfmisc_1(A_93, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_152, c_217])).
% 2.71/1.52  tff(c_148, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 2.71/1.52  tff(c_157, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_148])).
% 2.71/1.52  tff(c_48, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.52  tff(c_158, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10' | k2_zfmisc_1('#skF_11', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_149, c_48])).
% 2.71/1.52  tff(c_159, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_157, c_158])).
% 2.71/1.52  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_159])).
% 2.71/1.52  tff(c_237, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_147])).
% 2.71/1.52  tff(c_248, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_237, c_8])).
% 2.71/1.52  tff(c_16, plain, (![A_7, B_8, D_34]: (r2_hidden('#skF_7'(A_7, B_8, k2_zfmisc_1(A_7, B_8), D_34), A_7) | ~r2_hidden(D_34, k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.52  tff(c_241, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_237, c_6])).
% 2.71/1.52  tff(c_278, plain, (![A_115, B_116, D_117]: (r2_hidden('#skF_8'(A_115, B_116, k2_zfmisc_1(A_115, B_116), D_117), B_116) | ~r2_hidden(D_117, k2_zfmisc_1(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.52  tff(c_288, plain, (![B_121, D_122, A_123]: (~v1_xboole_0(B_121) | ~r2_hidden(D_122, k2_zfmisc_1(A_123, B_121)))), inference(resolution, [status(thm)], [c_278, c_2])).
% 2.71/1.52  tff(c_321, plain, (![B_126, A_127]: (~v1_xboole_0(B_126) | k2_zfmisc_1(A_127, B_126)='#skF_9')), inference(resolution, [status(thm)], [c_248, c_288])).
% 2.71/1.52  tff(c_347, plain, (![A_131]: (k2_zfmisc_1(A_131, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_241, c_321])).
% 2.71/1.52  tff(c_282, plain, (![B_116, D_117, A_115]: (~v1_xboole_0(B_116) | ~r2_hidden(D_117, k2_zfmisc_1(A_115, B_116)))), inference(resolution, [status(thm)], [c_278, c_2])).
% 2.71/1.52  tff(c_355, plain, (![D_117]: (~v1_xboole_0('#skF_9') | ~r2_hidden(D_117, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_347, c_282])).
% 2.71/1.52  tff(c_385, plain, (![D_132]: (~r2_hidden(D_132, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_355])).
% 2.71/1.52  tff(c_416, plain, (![D_133, B_134]: (~r2_hidden(D_133, k2_zfmisc_1('#skF_9', B_134)))), inference(resolution, [status(thm)], [c_16, c_385])).
% 2.71/1.52  tff(c_453, plain, (![B_134]: (k2_zfmisc_1('#skF_9', B_134)='#skF_9')), inference(resolution, [status(thm)], [c_248, c_416])).
% 2.71/1.52  tff(c_247, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_237, c_148])).
% 2.71/1.52  tff(c_260, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_237, c_237, c_48])).
% 2.71/1.52  tff(c_261, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_247, c_260])).
% 2.71/1.52  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_453, c_261])).
% 2.71/1.52  tff(c_460, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_40])).
% 2.71/1.52  tff(c_462, plain, (v1_xboole_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_6])).
% 2.71/1.52  tff(c_679, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_8])).
% 2.71/1.52  tff(c_710, plain, (![A_206, B_207, D_208]: (r2_hidden('#skF_8'(A_206, B_207, k2_zfmisc_1(A_206, B_207), D_208), B_207) | ~r2_hidden(D_208, k2_zfmisc_1(A_206, B_207)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.52  tff(c_715, plain, (![B_209, D_210, A_211]: (~v1_xboole_0(B_209) | ~r2_hidden(D_210, k2_zfmisc_1(A_211, B_209)))), inference(resolution, [status(thm)], [c_710, c_2])).
% 2.71/1.52  tff(c_743, plain, (![B_214, A_215]: (~v1_xboole_0(B_214) | k2_zfmisc_1(A_215, B_214)='#skF_12')), inference(resolution, [status(thm)], [c_679, c_715])).
% 2.71/1.52  tff(c_749, plain, (![A_215]: (k2_zfmisc_1(A_215, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_462, c_743])).
% 2.71/1.52  tff(c_605, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_8])).
% 2.71/1.52  tff(c_632, plain, (![A_178, B_179, D_180]: (r2_hidden('#skF_8'(A_178, B_179, k2_zfmisc_1(A_178, B_179), D_180), B_179) | ~r2_hidden(D_180, k2_zfmisc_1(A_178, B_179)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.52  tff(c_637, plain, (![B_181, D_182, A_183]: (~v1_xboole_0(B_181) | ~r2_hidden(D_182, k2_zfmisc_1(A_183, B_181)))), inference(resolution, [status(thm)], [c_632, c_2])).
% 2.71/1.52  tff(c_662, plain, (![B_186, A_187]: (~v1_xboole_0(B_186) | k2_zfmisc_1(A_187, B_186)='#skF_12')), inference(resolution, [status(thm)], [c_605, c_637])).
% 2.71/1.52  tff(c_668, plain, (![A_187]: (k2_zfmisc_1(A_187, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_462, c_662])).
% 2.71/1.52  tff(c_482, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_8])).
% 2.71/1.52  tff(c_556, plain, (![A_159, B_160, D_161]: (r2_hidden('#skF_7'(A_159, B_160, k2_zfmisc_1(A_159, B_160), D_161), A_159) | ~r2_hidden(D_161, k2_zfmisc_1(A_159, B_160)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.52  tff(c_461, plain, ('#skF_11'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_460, c_57])).
% 2.71/1.52  tff(c_471, plain, ('#skF_10'='#skF_12' | '#skF_9'='#skF_12' | k2_zfmisc_1('#skF_11', '#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_460, c_460, c_460, c_50])).
% 2.71/1.52  tff(c_472, plain, (k2_zfmisc_1('#skF_11', '#skF_12')='#skF_12'), inference(splitLeft, [status(thm)], [c_471])).
% 2.71/1.52  tff(c_505, plain, (![A_149, B_150, C_151, D_152]: (r2_hidden(k4_tarski(A_149, B_150), k2_zfmisc_1(C_151, D_152)) | ~r2_hidden(B_150, D_152) | ~r2_hidden(A_149, C_151))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.52  tff(c_521, plain, (![C_153, D_154, B_155, A_156]: (~v1_xboole_0(k2_zfmisc_1(C_153, D_154)) | ~r2_hidden(B_155, D_154) | ~r2_hidden(A_156, C_153))), inference(resolution, [status(thm)], [c_505, c_2])).
% 2.71/1.52  tff(c_523, plain, (![B_155, A_156]: (~v1_xboole_0('#skF_12') | ~r2_hidden(B_155, '#skF_12') | ~r2_hidden(A_156, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_472, c_521])).
% 2.71/1.52  tff(c_525, plain, (![B_155, A_156]: (~r2_hidden(B_155, '#skF_12') | ~r2_hidden(A_156, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_462, c_523])).
% 2.71/1.52  tff(c_528, plain, (![A_157]: (~r2_hidden(A_157, '#skF_11'))), inference(splitLeft, [status(thm)], [c_525])).
% 2.71/1.52  tff(c_532, plain, ('#skF_11'='#skF_12'), inference(resolution, [status(thm)], [c_482, c_528])).
% 2.71/1.52  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_461, c_532])).
% 2.71/1.52  tff(c_541, plain, (![B_155]: (~r2_hidden(B_155, '#skF_12'))), inference(splitRight, [status(thm)], [c_525])).
% 2.71/1.52  tff(c_570, plain, (![D_162, B_163]: (~r2_hidden(D_162, k2_zfmisc_1('#skF_12', B_163)))), inference(resolution, [status(thm)], [c_556, c_541])).
% 2.71/1.52  tff(c_589, plain, (![B_163]: (k2_zfmisc_1('#skF_12', B_163)='#skF_12')), inference(resolution, [status(thm)], [c_482, c_570])).
% 2.71/1.52  tff(c_42, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.52  tff(c_469, plain, ('#skF_10'='#skF_12' | '#skF_9'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_460, c_460, c_460, c_42])).
% 2.71/1.52  tff(c_470, plain, ('#skF_9'='#skF_12'), inference(splitLeft, [status(thm)], [c_469])).
% 2.71/1.52  tff(c_459, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.71/1.52  tff(c_467, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_460, c_459])).
% 2.71/1.52  tff(c_473, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_470, c_467])).
% 2.71/1.52  tff(c_594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_589, c_473])).
% 2.71/1.52  tff(c_596, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_12'), inference(splitRight, [status(thm)], [c_471])).
% 2.71/1.52  tff(c_671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_668, c_596])).
% 2.71/1.52  tff(c_672, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_469])).
% 2.71/1.52  tff(c_674, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_672, c_467])).
% 2.71/1.52  tff(c_762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_749, c_674])).
% 2.71/1.52  tff(c_764, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_46])).
% 2.71/1.52  tff(c_763, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_46])).
% 2.71/1.52  tff(c_770, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_764, c_764, c_763])).
% 2.71/1.52  tff(c_771, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_770])).
% 2.71/1.52  tff(c_765, plain, (v1_xboole_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_764, c_6])).
% 2.71/1.52  tff(c_772, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_765])).
% 2.71/1.52  tff(c_773, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_771, c_764])).
% 2.71/1.52  tff(c_785, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_773, c_8])).
% 2.71/1.52  tff(c_817, plain, (![A_237, B_238, D_239]: (r2_hidden('#skF_8'(A_237, B_238, k2_zfmisc_1(A_237, B_238), D_239), B_238) | ~r2_hidden(D_239, k2_zfmisc_1(A_237, B_238)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.52  tff(c_822, plain, (![B_240, D_241, A_242]: (~v1_xboole_0(B_240) | ~r2_hidden(D_241, k2_zfmisc_1(A_242, B_240)))), inference(resolution, [status(thm)], [c_817, c_2])).
% 2.71/1.52  tff(c_850, plain, (![B_245, A_246]: (~v1_xboole_0(B_245) | k2_zfmisc_1(A_246, B_245)='#skF_10')), inference(resolution, [status(thm)], [c_785, c_822])).
% 2.71/1.52  tff(c_856, plain, (![A_246]: (k2_zfmisc_1(A_246, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_772, c_850])).
% 2.71/1.52  tff(c_44, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.71/1.52  tff(c_798, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_773, c_771, c_773, c_44])).
% 2.71/1.52  tff(c_859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_856, c_798])).
% 2.71/1.52  tff(c_860, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_770])).
% 2.71/1.52  tff(c_863, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_860, c_764])).
% 2.71/1.52  tff(c_877, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_863, c_8])).
% 2.71/1.52  tff(c_995, plain, (![A_273, B_274, D_275]: (r2_hidden('#skF_7'(A_273, B_274, k2_zfmisc_1(A_273, B_274), D_275), A_273) | ~r2_hidden(D_275, k2_zfmisc_1(A_273, B_274)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.52  tff(c_862, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_860, c_765])).
% 2.71/1.52  tff(c_909, plain, (![A_261, B_262, D_263]: (r2_hidden('#skF_8'(A_261, B_262, k2_zfmisc_1(A_261, B_262), D_263), B_262) | ~r2_hidden(D_263, k2_zfmisc_1(A_261, B_262)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.52  tff(c_914, plain, (![B_264, D_265, A_266]: (~v1_xboole_0(B_264) | ~r2_hidden(D_265, k2_zfmisc_1(A_266, B_264)))), inference(resolution, [status(thm)], [c_909, c_2])).
% 2.71/1.52  tff(c_934, plain, (![B_267, A_268]: (~v1_xboole_0(B_267) | k2_zfmisc_1(A_268, B_267)='#skF_9')), inference(resolution, [status(thm)], [c_877, c_914])).
% 2.71/1.52  tff(c_938, plain, (![A_269]: (k2_zfmisc_1(A_269, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_862, c_934])).
% 2.71/1.52  tff(c_913, plain, (![B_262, D_263, A_261]: (~v1_xboole_0(B_262) | ~r2_hidden(D_263, k2_zfmisc_1(A_261, B_262)))), inference(resolution, [status(thm)], [c_909, c_2])).
% 2.71/1.52  tff(c_943, plain, (![D_263]: (~v1_xboole_0('#skF_9') | ~r2_hidden(D_263, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_938, c_913])).
% 2.71/1.52  tff(c_960, plain, (![D_263]: (~r2_hidden(D_263, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_862, c_943])).
% 2.71/1.52  tff(c_1014, plain, (![D_276, B_277]: (~r2_hidden(D_276, k2_zfmisc_1('#skF_9', B_277)))), inference(resolution, [status(thm)], [c_995, c_960])).
% 2.71/1.52  tff(c_1041, plain, (![B_277]: (k2_zfmisc_1('#skF_9', B_277)='#skF_9')), inference(resolution, [status(thm)], [c_877, c_1014])).
% 2.71/1.52  tff(c_890, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_863, c_860, c_863, c_44])).
% 2.71/1.52  tff(c_1046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1041, c_890])).
% 2.71/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.52  
% 2.71/1.52  Inference rules
% 2.71/1.52  ----------------------
% 2.71/1.52  #Ref     : 0
% 2.71/1.52  #Sup     : 197
% 2.71/1.52  #Fact    : 0
% 2.71/1.52  #Define  : 0
% 2.71/1.52  #Split   : 12
% 2.71/1.52  #Chain   : 0
% 2.71/1.52  #Close   : 0
% 2.71/1.52  
% 2.71/1.52  Ordering : KBO
% 2.71/1.52  
% 2.71/1.52  Simplification rules
% 2.71/1.52  ----------------------
% 2.71/1.52  #Subsume      : 35
% 2.71/1.52  #Demod        : 115
% 2.71/1.52  #Tautology    : 71
% 2.71/1.52  #SimpNegUnit  : 12
% 2.71/1.52  #BackRed      : 29
% 2.71/1.52  
% 2.71/1.52  #Partial instantiations: 0
% 2.71/1.52  #Strategies tried      : 1
% 2.71/1.52  
% 2.71/1.52  Timing (in seconds)
% 2.71/1.52  ----------------------
% 2.71/1.53  Preprocessing        : 0.35
% 2.71/1.53  Parsing              : 0.17
% 2.71/1.53  CNF conversion       : 0.03
% 2.71/1.53  Main loop            : 0.33
% 2.71/1.53  Inferencing          : 0.13
% 2.71/1.53  Reduction            : 0.08
% 2.71/1.53  Demodulation         : 0.06
% 2.71/1.53  BG Simplification    : 0.03
% 2.71/1.53  Subsumption          : 0.06
% 2.71/1.53  Abstraction          : 0.02
% 2.71/1.53  MUC search           : 0.00
% 2.71/1.53  Cooper               : 0.00
% 2.71/1.53  Total                : 0.74
% 2.71/1.53  Index Insertion      : 0.00
% 2.71/1.53  Index Deletion       : 0.00
% 2.71/1.53  Index Matching       : 0.00
% 2.71/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
