%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:40 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  198 (1008 expanded)
%              Number of leaves         :   30 ( 314 expanded)
%              Depth                    :   13
%              Number of atoms          :  286 (2119 expanded)
%              Number of equality atoms :   95 (1079 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_12

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_12,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_659,plain,(
    ! [B_164,A_165] :
      ( ~ r1_xboole_0(B_164,A_165)
      | ~ r1_tarski(B_164,A_165)
      | v1_xboole_0(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_662,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_659])).

tff(c_665,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_662])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_81,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_75,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_84,plain,(
    ! [B_57,A_58] :
      ( ~ r1_xboole_0(B_57,A_58)
      | ~ r1_tarski(B_57,A_58)
      | v1_xboole_0(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_87,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_84])).

tff(c_90,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_87])).

tff(c_134,plain,(
    ! [A_77,B_78,D_79] :
      ( r2_hidden('#skF_8'(A_77,B_78,k2_zfmisc_1(A_77,B_78),D_79),B_78)
      | ~ r2_hidden(D_79,k2_zfmisc_1(A_77,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ! [B_80,D_81,A_82] :
      ( ~ v1_xboole_0(B_80)
      | ~ r2_hidden(D_81,k2_zfmisc_1(A_82,B_80)) ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_182,plain,(
    ! [B_85,A_86] :
      ( ~ v1_xboole_0(B_85)
      | k2_zfmisc_1(A_86,B_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_143])).

tff(c_186,plain,(
    ! [A_87] : k2_zfmisc_1(A_87,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_182])).

tff(c_141,plain,(
    ! [B_78,D_79,A_77] :
      ( ~ v1_xboole_0(B_78)
      | ~ r2_hidden(D_79,k2_zfmisc_1(A_77,B_78)) ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_191,plain,(
    ! [D_79] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_79,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_141])).

tff(c_208,plain,(
    ! [D_79] : ~ r2_hidden(D_79,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_191])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_96,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_118,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( r2_hidden(k4_tarski(A_73,B_74),k2_zfmisc_1(C_75,D_76))
      | ~ r2_hidden(B_74,D_76)
      | ~ r2_hidden(A_73,C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_130,plain,(
    ! [A_73,B_74] :
      ( r2_hidden(k4_tarski(A_73,B_74),k1_xboole_0)
      | ~ r2_hidden(B_74,'#skF_12')
      | ~ r2_hidden(A_73,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_118])).

tff(c_211,plain,(
    ! [B_74,A_73] :
      ( ~ r2_hidden(B_74,'#skF_12')
      | ~ r2_hidden(A_73,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_130])).

tff(c_232,plain,(
    ! [A_89] : ~ r2_hidden(A_89,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_240,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_6,c_232])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_240])).

tff(c_274,plain,(
    ! [B_93] : ~ r2_hidden(B_93,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_286,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6,c_274])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_286])).

tff(c_297,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_299,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_304,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_6])).

tff(c_24,plain,(
    ! [A_12,B_13,D_39] :
      ( r2_hidden('#skF_8'(A_12,B_13,k2_zfmisc_1(A_12,B_13),D_39),B_13)
      | ~ r2_hidden(D_39,k2_zfmisc_1(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_300,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_90])).

tff(c_359,plain,(
    ! [A_115,B_116,D_117] :
      ( r2_hidden('#skF_7'(A_115,B_116,k2_zfmisc_1(A_115,B_116),D_117),A_115)
      | ~ r2_hidden(D_117,k2_zfmisc_1(A_115,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_364,plain,(
    ! [A_118,D_119,B_120] :
      ( ~ v1_xboole_0(A_118)
      | ~ r2_hidden(D_119,k2_zfmisc_1(A_118,B_120)) ) ),
    inference(resolution,[status(thm)],[c_359,c_2])).

tff(c_402,plain,(
    ! [A_126,B_127] :
      ( ~ v1_xboole_0(A_126)
      | k2_zfmisc_1(A_126,B_127) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_304,c_364])).

tff(c_409,plain,(
    ! [B_128] : k2_zfmisc_1('#skF_10',B_128) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_300,c_402])).

tff(c_363,plain,(
    ! [A_115,D_117,B_116] :
      ( ~ v1_xboole_0(A_115)
      | ~ r2_hidden(D_117,k2_zfmisc_1(A_115,B_116)) ) ),
    inference(resolution,[status(thm)],[c_359,c_2])).

tff(c_420,plain,(
    ! [D_117] :
      ( ~ v1_xboole_0('#skF_10')
      | ~ r2_hidden(D_117,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_363])).

tff(c_466,plain,(
    ! [D_132] : ~ r2_hidden(D_132,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_420])).

tff(c_497,plain,(
    ! [D_133,A_134] : ~ r2_hidden(D_133,k2_zfmisc_1(A_134,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_24,c_466])).

tff(c_534,plain,(
    ! [A_134] : k2_zfmisc_1(A_134,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_304,c_497])).

tff(c_58,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_83,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_301,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_83])).

tff(c_539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_301])).

tff(c_540,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_543,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_90])).

tff(c_547,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_6])).

tff(c_601,plain,(
    ! [A_152,B_153,D_154] :
      ( r2_hidden('#skF_7'(A_152,B_153,k2_zfmisc_1(A_152,B_153),D_154),A_152)
      | ~ r2_hidden(D_154,k2_zfmisc_1(A_152,B_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_606,plain,(
    ! [A_155,D_156,B_157] :
      ( ~ v1_xboole_0(A_155)
      | ~ r2_hidden(D_156,k2_zfmisc_1(A_155,B_157)) ) ),
    inference(resolution,[status(thm)],[c_601,c_2])).

tff(c_631,plain,(
    ! [A_160,B_161] :
      ( ~ v1_xboole_0(A_160)
      | k2_zfmisc_1(A_160,B_161) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_547,c_606])).

tff(c_637,plain,(
    ! [B_161] : k2_zfmisc_1('#skF_9',B_161) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_543,c_631])).

tff(c_544,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_83])).

tff(c_640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_544])).

tff(c_642,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_688,plain,(
    ! [A_180,B_181,C_182,D_183] :
      ( r2_hidden(k4_tarski(A_180,B_181),k2_zfmisc_1(C_182,D_183))
      | ~ r2_hidden(B_181,D_183)
      | ~ r2_hidden(A_180,C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_708,plain,(
    ! [C_186,D_187,B_188,A_189] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_186,D_187))
      | ~ r2_hidden(B_188,D_187)
      | ~ r2_hidden(A_189,C_186) ) ),
    inference(resolution,[status(thm)],[c_688,c_2])).

tff(c_710,plain,(
    ! [B_188,A_189] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(B_188,'#skF_10')
      | ~ r2_hidden(A_189,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_708])).

tff(c_714,plain,(
    ! [B_188,A_189] :
      ( ~ r2_hidden(B_188,'#skF_10')
      | ~ r2_hidden(A_189,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_710])).

tff(c_742,plain,(
    ! [A_192] : ~ r2_hidden(A_192,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_714])).

tff(c_751,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6,c_742])).

tff(c_761,plain,(
    '#skF_9' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_81])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_763,plain,(
    '#skF_11' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_75])).

tff(c_641,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_712,plain,(
    ! [B_188,A_189] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(B_188,'#skF_12')
      | ~ r2_hidden(A_189,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_708])).

tff(c_716,plain,(
    ! [B_188,A_189] :
      ( ~ r2_hidden(B_188,'#skF_12')
      | ~ r2_hidden(A_189,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_712])).

tff(c_1006,plain,(
    ! [A_209] : ~ r2_hidden(A_209,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_716])).

tff(c_1021,plain,(
    v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_1006])).

tff(c_76,plain,(
    ! [A_55] :
      ( r2_hidden('#skF_2'(A_55),A_55)
      | k1_xboole_0 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(A_55)
      | k1_xboole_0 = A_55 ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_760,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(A_55)
      | A_55 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_80])).

tff(c_1024,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1021,c_760])).

tff(c_1028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_763,c_1024])).

tff(c_1030,plain,(
    ! [B_210] : ~ r2_hidden(B_210,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_716])).

tff(c_1045,plain,(
    v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_4,c_1030])).

tff(c_1071,plain,(
    '#skF_9' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1045,c_760])).

tff(c_1075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_761,c_1071])).

tff(c_1078,plain,(
    ! [B_214] : ~ r2_hidden(B_214,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_714])).

tff(c_1087,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6,c_1078])).

tff(c_1096,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_81])).

tff(c_1098,plain,(
    '#skF_11' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_75])).

tff(c_1076,plain,(
    ! [B_188] : ~ r2_hidden(B_188,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_714])).

tff(c_703,plain,(
    ! [A_180,B_181] :
      ( r2_hidden(k4_tarski(A_180,B_181),k1_xboole_0)
      | ~ r2_hidden(B_181,'#skF_12')
      | ~ r2_hidden(A_180,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_688])).

tff(c_1174,plain,(
    ! [A_180,B_181] :
      ( r2_hidden(k4_tarski(A_180,B_181),'#skF_10')
      | ~ r2_hidden(B_181,'#skF_12')
      | ~ r2_hidden(A_180,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_703])).

tff(c_1175,plain,(
    ! [B_181,A_180] :
      ( ~ r2_hidden(B_181,'#skF_12')
      | ~ r2_hidden(A_180,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1076,c_1174])).

tff(c_1177,plain,(
    ! [A_219] : ~ r2_hidden(A_219,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_1175])).

tff(c_1187,plain,(
    v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_1177])).

tff(c_1095,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(A_55)
      | A_55 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_80])).

tff(c_1190,plain,(
    '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1187,c_1095])).

tff(c_1194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1098,c_1190])).

tff(c_1196,plain,(
    ! [B_220] : ~ r2_hidden(B_220,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_1175])).

tff(c_1206,plain,(
    v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_4,c_1196])).

tff(c_1209,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1206,c_1095])).

tff(c_1213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1096,c_1209])).

tff(c_1215,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1216,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_6])).

tff(c_1219,plain,(
    r1_xboole_0('#skF_12','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_1215,c_14])).

tff(c_1355,plain,(
    ! [B_259,A_260] :
      ( ~ r1_xboole_0(B_259,A_260)
      | ~ r1_tarski(B_259,A_260)
      | v1_xboole_0(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1358,plain,
    ( ~ r1_tarski('#skF_12','#skF_12')
    | v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_1219,c_1355])).

tff(c_1361,plain,(
    v1_xboole_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1358])).

tff(c_1392,plain,(
    ! [A_279,B_280,D_281] :
      ( r2_hidden('#skF_7'(A_279,B_280,k2_zfmisc_1(A_279,B_280),D_281),A_279)
      | ~ r2_hidden(D_281,k2_zfmisc_1(A_279,B_280)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1397,plain,(
    ! [A_282,D_283,B_284] :
      ( ~ v1_xboole_0(A_282)
      | ~ r2_hidden(D_283,k2_zfmisc_1(A_282,B_284)) ) ),
    inference(resolution,[status(thm)],[c_1392,c_2])).

tff(c_1435,plain,(
    ! [A_290,B_291] :
      ( ~ v1_xboole_0(A_290)
      | k2_zfmisc_1(A_290,B_291) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_1216,c_1397])).

tff(c_1442,plain,(
    ! [B_292] : k2_zfmisc_1('#skF_12',B_292) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1361,c_1435])).

tff(c_1396,plain,(
    ! [A_279,D_281,B_280] :
      ( ~ v1_xboole_0(A_279)
      | ~ r2_hidden(D_281,k2_zfmisc_1(A_279,B_280)) ) ),
    inference(resolution,[status(thm)],[c_1392,c_2])).

tff(c_1453,plain,(
    ! [D_281] :
      ( ~ v1_xboole_0('#skF_12')
      | ~ r2_hidden(D_281,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_1396])).

tff(c_1490,plain,(
    ! [D_296] : ~ r2_hidden(D_296,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_1453])).

tff(c_1519,plain,(
    ! [D_297,A_298] : ~ r2_hidden(D_297,k2_zfmisc_1(A_298,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_24,c_1490])).

tff(c_1551,plain,(
    ! [A_298] : k2_zfmisc_1(A_298,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1216,c_1519])).

tff(c_1247,plain,(
    ! [B_224,A_225] :
      ( ~ r1_xboole_0(B_224,A_225)
      | ~ r1_tarski(B_224,A_225)
      | v1_xboole_0(B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1250,plain,
    ( ~ r1_tarski('#skF_12','#skF_12')
    | v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_1219,c_1247])).

tff(c_1253,plain,(
    v1_xboole_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1250])).

tff(c_1283,plain,(
    ! [A_244,B_245,D_246] :
      ( r2_hidden('#skF_7'(A_244,B_245,k2_zfmisc_1(A_244,B_245),D_246),A_244)
      | ~ r2_hidden(D_246,k2_zfmisc_1(A_244,B_245)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1288,plain,(
    ! [A_247,D_248,B_249] :
      ( ~ v1_xboole_0(A_247)
      | ~ r2_hidden(D_248,k2_zfmisc_1(A_247,B_249)) ) ),
    inference(resolution,[status(thm)],[c_1283,c_2])).

tff(c_1326,plain,(
    ! [A_255,B_256] :
      ( ~ v1_xboole_0(A_255)
      | k2_zfmisc_1(A_255,B_256) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_1216,c_1288])).

tff(c_1332,plain,(
    ! [B_256] : k2_zfmisc_1('#skF_12',B_256) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1253,c_1326])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1228,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_9' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_1215,c_1215,c_52])).

tff(c_1229,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_1228])).

tff(c_1214,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1224,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_1214])).

tff(c_1230,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_1224])).

tff(c_1335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1230])).

tff(c_1336,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_1228])).

tff(c_1339,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_1224])).

tff(c_1556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_1339])).

tff(c_1558,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1557,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1565,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1558,c_1557])).

tff(c_1566,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1565])).

tff(c_1568,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1566,c_1558])).

tff(c_1586,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_6])).

tff(c_1560,plain,(
    r1_xboole_0('#skF_11','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1558,c_14])).

tff(c_1567,plain,(
    r1_xboole_0('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1566,c_1566,c_1560])).

tff(c_1604,plain,(
    ! [B_304,A_305] :
      ( ~ r1_xboole_0(B_304,A_305)
      | ~ r1_tarski(B_304,A_305)
      | v1_xboole_0(B_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1607,plain,
    ( ~ r1_tarski('#skF_10','#skF_10')
    | v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_1567,c_1604])).

tff(c_1610,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1607])).

tff(c_1632,plain,(
    ! [A_322,B_323,D_324] :
      ( r2_hidden('#skF_7'(A_322,B_323,k2_zfmisc_1(A_322,B_323),D_324),A_322)
      | ~ r2_hidden(D_324,k2_zfmisc_1(A_322,B_323)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1642,plain,(
    ! [A_328,D_329,B_330] :
      ( ~ v1_xboole_0(A_328)
      | ~ r2_hidden(D_329,k2_zfmisc_1(A_328,B_330)) ) ),
    inference(resolution,[status(thm)],[c_1632,c_2])).

tff(c_1675,plain,(
    ! [A_333,B_334] :
      ( ~ v1_xboole_0(A_333)
      | k2_zfmisc_1(A_333,B_334) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1586,c_1642])).

tff(c_1692,plain,(
    ! [B_338] : k2_zfmisc_1('#skF_10',B_338) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1610,c_1675])).

tff(c_1636,plain,(
    ! [A_322,D_324,B_323] :
      ( ~ v1_xboole_0(A_322)
      | ~ r2_hidden(D_324,k2_zfmisc_1(A_322,B_323)) ) ),
    inference(resolution,[status(thm)],[c_1632,c_2])).

tff(c_1700,plain,(
    ! [D_324] :
      ( ~ v1_xboole_0('#skF_10')
      | ~ r2_hidden(D_324,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1692,c_1636])).

tff(c_1730,plain,(
    ! [D_339] : ~ r2_hidden(D_339,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1610,c_1700])).

tff(c_1759,plain,(
    ! [D_340,A_341] : ~ r2_hidden(D_340,k2_zfmisc_1(A_341,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_24,c_1730])).

tff(c_1791,plain,(
    ! [A_341] : k2_zfmisc_1(A_341,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1586,c_1759])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1578,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_1566,c_1568,c_54])).

tff(c_1796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1791,c_1578])).

tff(c_1797,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1565])).

tff(c_1799,plain,(
    r1_xboole_0('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1797,c_1797,c_1560])).

tff(c_1830,plain,(
    ! [B_345,A_346] :
      ( ~ r1_xboole_0(B_345,A_346)
      | ~ r1_tarski(B_345,A_346)
      | v1_xboole_0(B_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1833,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1799,c_1830])).

tff(c_1836,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1833])).

tff(c_1800,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1797,c_1558])).

tff(c_1822,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | A_5 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1800,c_6])).

tff(c_1867,plain,(
    ! [A_365,B_366,D_367] :
      ( r2_hidden('#skF_7'(A_365,B_366,k2_zfmisc_1(A_365,B_366),D_367),A_365)
      | ~ r2_hidden(D_367,k2_zfmisc_1(A_365,B_366)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1872,plain,(
    ! [A_368,D_369,B_370] :
      ( ~ v1_xboole_0(A_368)
      | ~ r2_hidden(D_369,k2_zfmisc_1(A_368,B_370)) ) ),
    inference(resolution,[status(thm)],[c_1867,c_2])).

tff(c_1902,plain,(
    ! [A_374,B_375] :
      ( ~ v1_xboole_0(A_374)
      | k2_zfmisc_1(A_374,B_375) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1822,c_1872])).

tff(c_1905,plain,(
    ! [B_375] : k2_zfmisc_1('#skF_9',B_375) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1836,c_1902])).

tff(c_1818,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1800,c_1797,c_1800,c_54])).

tff(c_1908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1905,c_1818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:49:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.56  
% 3.27/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.56  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_12
% 3.41/1.56  
% 3.41/1.56  %Foreground sorts:
% 3.41/1.56  
% 3.41/1.56  
% 3.41/1.56  %Background operators:
% 3.41/1.56  
% 3.41/1.56  
% 3.41/1.56  %Foreground operators:
% 3.41/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.41/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.56  tff('#skF_11', type, '#skF_11': $i).
% 3.41/1.56  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.41/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.41/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.41/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.41/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.56  tff('#skF_10', type, '#skF_10': $i).
% 3.41/1.56  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.41/1.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.41/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.41/1.56  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.41/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.41/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.41/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.41/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.41/1.56  tff('#skF_12', type, '#skF_12': $i).
% 3.41/1.56  
% 3.41/1.59  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.41/1.59  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.41/1.59  tff(f_57, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.41/1.59  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.41/1.59  tff(f_90, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.41/1.59  tff(f_77, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.41/1.59  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.41/1.59  tff(f_83, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.41/1.59  tff(c_12, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.41/1.59  tff(c_6, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.41/1.59  tff(c_14, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.41/1.59  tff(c_659, plain, (![B_164, A_165]: (~r1_xboole_0(B_164, A_165) | ~r1_tarski(B_164, A_165) | v1_xboole_0(B_164))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.41/1.59  tff(c_662, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_659])).
% 3.41/1.59  tff(c_665, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_662])).
% 3.41/1.59  tff(c_50, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.41/1.59  tff(c_81, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_50])).
% 3.41/1.59  tff(c_56, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.41/1.59  tff(c_75, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_56])).
% 3.41/1.59  tff(c_84, plain, (![B_57, A_58]: (~r1_xboole_0(B_57, A_58) | ~r1_tarski(B_57, A_58) | v1_xboole_0(B_57))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.41/1.59  tff(c_87, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_84])).
% 3.41/1.59  tff(c_90, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_87])).
% 3.41/1.59  tff(c_134, plain, (![A_77, B_78, D_79]: (r2_hidden('#skF_8'(A_77, B_78, k2_zfmisc_1(A_77, B_78), D_79), B_78) | ~r2_hidden(D_79, k2_zfmisc_1(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.41/1.59  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.41/1.59  tff(c_143, plain, (![B_80, D_81, A_82]: (~v1_xboole_0(B_80) | ~r2_hidden(D_81, k2_zfmisc_1(A_82, B_80)))), inference(resolution, [status(thm)], [c_134, c_2])).
% 3.41/1.59  tff(c_182, plain, (![B_85, A_86]: (~v1_xboole_0(B_85) | k2_zfmisc_1(A_86, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_143])).
% 3.41/1.59  tff(c_186, plain, (![A_87]: (k2_zfmisc_1(A_87, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_90, c_182])).
% 3.41/1.59  tff(c_141, plain, (![B_78, D_79, A_77]: (~v1_xboole_0(B_78) | ~r2_hidden(D_79, k2_zfmisc_1(A_77, B_78)))), inference(resolution, [status(thm)], [c_134, c_2])).
% 3.41/1.59  tff(c_191, plain, (![D_79]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(D_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_186, c_141])).
% 3.41/1.59  tff(c_208, plain, (![D_79]: (~r2_hidden(D_79, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_191])).
% 3.41/1.59  tff(c_60, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.41/1.59  tff(c_96, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 3.41/1.59  tff(c_118, plain, (![A_73, B_74, C_75, D_76]: (r2_hidden(k4_tarski(A_73, B_74), k2_zfmisc_1(C_75, D_76)) | ~r2_hidden(B_74, D_76) | ~r2_hidden(A_73, C_75))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.41/1.59  tff(c_130, plain, (![A_73, B_74]: (r2_hidden(k4_tarski(A_73, B_74), k1_xboole_0) | ~r2_hidden(B_74, '#skF_12') | ~r2_hidden(A_73, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_118])).
% 3.41/1.59  tff(c_211, plain, (![B_74, A_73]: (~r2_hidden(B_74, '#skF_12') | ~r2_hidden(A_73, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_208, c_130])).
% 3.41/1.59  tff(c_232, plain, (![A_89]: (~r2_hidden(A_89, '#skF_11'))), inference(splitLeft, [status(thm)], [c_211])).
% 3.41/1.59  tff(c_240, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_6, c_232])).
% 3.41/1.59  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_240])).
% 3.41/1.59  tff(c_274, plain, (![B_93]: (~r2_hidden(B_93, '#skF_12'))), inference(splitRight, [status(thm)], [c_211])).
% 3.41/1.59  tff(c_286, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_6, c_274])).
% 3.41/1.59  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_286])).
% 3.41/1.59  tff(c_297, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_60])).
% 3.41/1.59  tff(c_299, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_297])).
% 3.41/1.59  tff(c_304, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_6])).
% 3.41/1.59  tff(c_24, plain, (![A_12, B_13, D_39]: (r2_hidden('#skF_8'(A_12, B_13, k2_zfmisc_1(A_12, B_13), D_39), B_13) | ~r2_hidden(D_39, k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.41/1.59  tff(c_300, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_90])).
% 3.41/1.59  tff(c_359, plain, (![A_115, B_116, D_117]: (r2_hidden('#skF_7'(A_115, B_116, k2_zfmisc_1(A_115, B_116), D_117), A_115) | ~r2_hidden(D_117, k2_zfmisc_1(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.41/1.59  tff(c_364, plain, (![A_118, D_119, B_120]: (~v1_xboole_0(A_118) | ~r2_hidden(D_119, k2_zfmisc_1(A_118, B_120)))), inference(resolution, [status(thm)], [c_359, c_2])).
% 3.41/1.59  tff(c_402, plain, (![A_126, B_127]: (~v1_xboole_0(A_126) | k2_zfmisc_1(A_126, B_127)='#skF_10')), inference(resolution, [status(thm)], [c_304, c_364])).
% 3.41/1.59  tff(c_409, plain, (![B_128]: (k2_zfmisc_1('#skF_10', B_128)='#skF_10')), inference(resolution, [status(thm)], [c_300, c_402])).
% 3.41/1.59  tff(c_363, plain, (![A_115, D_117, B_116]: (~v1_xboole_0(A_115) | ~r2_hidden(D_117, k2_zfmisc_1(A_115, B_116)))), inference(resolution, [status(thm)], [c_359, c_2])).
% 3.41/1.59  tff(c_420, plain, (![D_117]: (~v1_xboole_0('#skF_10') | ~r2_hidden(D_117, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_363])).
% 3.41/1.59  tff(c_466, plain, (![D_132]: (~r2_hidden(D_132, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_300, c_420])).
% 3.41/1.59  tff(c_497, plain, (![D_133, A_134]: (~r2_hidden(D_133, k2_zfmisc_1(A_134, '#skF_10')))), inference(resolution, [status(thm)], [c_24, c_466])).
% 3.41/1.59  tff(c_534, plain, (![A_134]: (k2_zfmisc_1(A_134, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_304, c_497])).
% 3.41/1.59  tff(c_58, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.41/1.59  tff(c_83, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 3.41/1.59  tff(c_301, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_83])).
% 3.41/1.59  tff(c_539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_534, c_301])).
% 3.41/1.59  tff(c_540, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_297])).
% 3.41/1.59  tff(c_543, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_540, c_90])).
% 3.41/1.59  tff(c_547, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_540, c_6])).
% 3.41/1.59  tff(c_601, plain, (![A_152, B_153, D_154]: (r2_hidden('#skF_7'(A_152, B_153, k2_zfmisc_1(A_152, B_153), D_154), A_152) | ~r2_hidden(D_154, k2_zfmisc_1(A_152, B_153)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.41/1.59  tff(c_606, plain, (![A_155, D_156, B_157]: (~v1_xboole_0(A_155) | ~r2_hidden(D_156, k2_zfmisc_1(A_155, B_157)))), inference(resolution, [status(thm)], [c_601, c_2])).
% 3.41/1.59  tff(c_631, plain, (![A_160, B_161]: (~v1_xboole_0(A_160) | k2_zfmisc_1(A_160, B_161)='#skF_9')), inference(resolution, [status(thm)], [c_547, c_606])).
% 3.41/1.59  tff(c_637, plain, (![B_161]: (k2_zfmisc_1('#skF_9', B_161)='#skF_9')), inference(resolution, [status(thm)], [c_543, c_631])).
% 3.41/1.59  tff(c_544, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_540, c_83])).
% 3.41/1.59  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_637, c_544])).
% 3.41/1.59  tff(c_642, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 3.41/1.59  tff(c_688, plain, (![A_180, B_181, C_182, D_183]: (r2_hidden(k4_tarski(A_180, B_181), k2_zfmisc_1(C_182, D_183)) | ~r2_hidden(B_181, D_183) | ~r2_hidden(A_180, C_182))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.41/1.59  tff(c_708, plain, (![C_186, D_187, B_188, A_189]: (~v1_xboole_0(k2_zfmisc_1(C_186, D_187)) | ~r2_hidden(B_188, D_187) | ~r2_hidden(A_189, C_186))), inference(resolution, [status(thm)], [c_688, c_2])).
% 3.41/1.59  tff(c_710, plain, (![B_188, A_189]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(B_188, '#skF_10') | ~r2_hidden(A_189, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_642, c_708])).
% 3.41/1.59  tff(c_714, plain, (![B_188, A_189]: (~r2_hidden(B_188, '#skF_10') | ~r2_hidden(A_189, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_665, c_710])).
% 3.41/1.59  tff(c_742, plain, (![A_192]: (~r2_hidden(A_192, '#skF_9'))), inference(splitLeft, [status(thm)], [c_714])).
% 3.41/1.59  tff(c_751, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_6, c_742])).
% 3.41/1.59  tff(c_761, plain, ('#skF_9'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_751, c_81])).
% 3.41/1.59  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.41/1.59  tff(c_763, plain, ('#skF_11'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_751, c_75])).
% 3.41/1.59  tff(c_641, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 3.41/1.59  tff(c_712, plain, (![B_188, A_189]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(B_188, '#skF_12') | ~r2_hidden(A_189, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_641, c_708])).
% 3.41/1.59  tff(c_716, plain, (![B_188, A_189]: (~r2_hidden(B_188, '#skF_12') | ~r2_hidden(A_189, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_665, c_712])).
% 3.41/1.59  tff(c_1006, plain, (![A_209]: (~r2_hidden(A_209, '#skF_11'))), inference(splitLeft, [status(thm)], [c_716])).
% 3.41/1.59  tff(c_1021, plain, (v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_4, c_1006])).
% 3.41/1.59  tff(c_76, plain, (![A_55]: (r2_hidden('#skF_2'(A_55), A_55) | k1_xboole_0=A_55)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.41/1.59  tff(c_80, plain, (![A_55]: (~v1_xboole_0(A_55) | k1_xboole_0=A_55)), inference(resolution, [status(thm)], [c_76, c_2])).
% 3.41/1.59  tff(c_760, plain, (![A_55]: (~v1_xboole_0(A_55) | A_55='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_751, c_80])).
% 3.41/1.59  tff(c_1024, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_1021, c_760])).
% 3.41/1.59  tff(c_1028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_763, c_1024])).
% 3.41/1.59  tff(c_1030, plain, (![B_210]: (~r2_hidden(B_210, '#skF_12'))), inference(splitRight, [status(thm)], [c_716])).
% 3.41/1.59  tff(c_1045, plain, (v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_4, c_1030])).
% 3.41/1.59  tff(c_1071, plain, ('#skF_9'='#skF_12'), inference(resolution, [status(thm)], [c_1045, c_760])).
% 3.41/1.59  tff(c_1075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_761, c_1071])).
% 3.41/1.59  tff(c_1078, plain, (![B_214]: (~r2_hidden(B_214, '#skF_10'))), inference(splitRight, [status(thm)], [c_714])).
% 3.41/1.59  tff(c_1087, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_6, c_1078])).
% 3.41/1.59  tff(c_1096, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_81])).
% 3.41/1.59  tff(c_1098, plain, ('#skF_11'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_75])).
% 3.41/1.59  tff(c_1076, plain, (![B_188]: (~r2_hidden(B_188, '#skF_10'))), inference(splitRight, [status(thm)], [c_714])).
% 3.41/1.59  tff(c_703, plain, (![A_180, B_181]: (r2_hidden(k4_tarski(A_180, B_181), k1_xboole_0) | ~r2_hidden(B_181, '#skF_12') | ~r2_hidden(A_180, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_641, c_688])).
% 3.41/1.59  tff(c_1174, plain, (![A_180, B_181]: (r2_hidden(k4_tarski(A_180, B_181), '#skF_10') | ~r2_hidden(B_181, '#skF_12') | ~r2_hidden(A_180, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_703])).
% 3.41/1.59  tff(c_1175, plain, (![B_181, A_180]: (~r2_hidden(B_181, '#skF_12') | ~r2_hidden(A_180, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_1076, c_1174])).
% 3.41/1.59  tff(c_1177, plain, (![A_219]: (~r2_hidden(A_219, '#skF_11'))), inference(splitLeft, [status(thm)], [c_1175])).
% 3.41/1.59  tff(c_1187, plain, (v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_4, c_1177])).
% 3.41/1.59  tff(c_1095, plain, (![A_55]: (~v1_xboole_0(A_55) | A_55='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_80])).
% 3.41/1.59  tff(c_1190, plain, ('#skF_11'='#skF_10'), inference(resolution, [status(thm)], [c_1187, c_1095])).
% 3.41/1.59  tff(c_1194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1098, c_1190])).
% 3.41/1.59  tff(c_1196, plain, (![B_220]: (~r2_hidden(B_220, '#skF_12'))), inference(splitRight, [status(thm)], [c_1175])).
% 3.41/1.59  tff(c_1206, plain, (v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_4, c_1196])).
% 3.41/1.59  tff(c_1209, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_1206, c_1095])).
% 3.41/1.59  tff(c_1213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1096, c_1209])).
% 3.41/1.59  tff(c_1215, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_50])).
% 3.41/1.59  tff(c_1216, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_6])).
% 3.41/1.59  tff(c_1219, plain, (r1_xboole_0('#skF_12', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_1215, c_14])).
% 3.41/1.59  tff(c_1355, plain, (![B_259, A_260]: (~r1_xboole_0(B_259, A_260) | ~r1_tarski(B_259, A_260) | v1_xboole_0(B_259))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.41/1.59  tff(c_1358, plain, (~r1_tarski('#skF_12', '#skF_12') | v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_1219, c_1355])).
% 3.41/1.59  tff(c_1361, plain, (v1_xboole_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1358])).
% 3.41/1.59  tff(c_1392, plain, (![A_279, B_280, D_281]: (r2_hidden('#skF_7'(A_279, B_280, k2_zfmisc_1(A_279, B_280), D_281), A_279) | ~r2_hidden(D_281, k2_zfmisc_1(A_279, B_280)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.41/1.59  tff(c_1397, plain, (![A_282, D_283, B_284]: (~v1_xboole_0(A_282) | ~r2_hidden(D_283, k2_zfmisc_1(A_282, B_284)))), inference(resolution, [status(thm)], [c_1392, c_2])).
% 3.41/1.59  tff(c_1435, plain, (![A_290, B_291]: (~v1_xboole_0(A_290) | k2_zfmisc_1(A_290, B_291)='#skF_12')), inference(resolution, [status(thm)], [c_1216, c_1397])).
% 3.41/1.59  tff(c_1442, plain, (![B_292]: (k2_zfmisc_1('#skF_12', B_292)='#skF_12')), inference(resolution, [status(thm)], [c_1361, c_1435])).
% 3.41/1.59  tff(c_1396, plain, (![A_279, D_281, B_280]: (~v1_xboole_0(A_279) | ~r2_hidden(D_281, k2_zfmisc_1(A_279, B_280)))), inference(resolution, [status(thm)], [c_1392, c_2])).
% 3.41/1.59  tff(c_1453, plain, (![D_281]: (~v1_xboole_0('#skF_12') | ~r2_hidden(D_281, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1442, c_1396])).
% 3.41/1.59  tff(c_1490, plain, (![D_296]: (~r2_hidden(D_296, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_1453])).
% 3.41/1.59  tff(c_1519, plain, (![D_297, A_298]: (~r2_hidden(D_297, k2_zfmisc_1(A_298, '#skF_12')))), inference(resolution, [status(thm)], [c_24, c_1490])).
% 3.41/1.59  tff(c_1551, plain, (![A_298]: (k2_zfmisc_1(A_298, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_1216, c_1519])).
% 3.41/1.59  tff(c_1247, plain, (![B_224, A_225]: (~r1_xboole_0(B_224, A_225) | ~r1_tarski(B_224, A_225) | v1_xboole_0(B_224))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.41/1.59  tff(c_1250, plain, (~r1_tarski('#skF_12', '#skF_12') | v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_1219, c_1247])).
% 3.41/1.59  tff(c_1253, plain, (v1_xboole_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1250])).
% 3.41/1.59  tff(c_1283, plain, (![A_244, B_245, D_246]: (r2_hidden('#skF_7'(A_244, B_245, k2_zfmisc_1(A_244, B_245), D_246), A_244) | ~r2_hidden(D_246, k2_zfmisc_1(A_244, B_245)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.41/1.59  tff(c_1288, plain, (![A_247, D_248, B_249]: (~v1_xboole_0(A_247) | ~r2_hidden(D_248, k2_zfmisc_1(A_247, B_249)))), inference(resolution, [status(thm)], [c_1283, c_2])).
% 3.41/1.59  tff(c_1326, plain, (![A_255, B_256]: (~v1_xboole_0(A_255) | k2_zfmisc_1(A_255, B_256)='#skF_12')), inference(resolution, [status(thm)], [c_1216, c_1288])).
% 3.41/1.59  tff(c_1332, plain, (![B_256]: (k2_zfmisc_1('#skF_12', B_256)='#skF_12')), inference(resolution, [status(thm)], [c_1253, c_1326])).
% 3.41/1.59  tff(c_52, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.41/1.59  tff(c_1228, plain, ('#skF_10'='#skF_12' | '#skF_9'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_1215, c_1215, c_52])).
% 3.41/1.59  tff(c_1229, plain, ('#skF_9'='#skF_12'), inference(splitLeft, [status(thm)], [c_1228])).
% 3.41/1.59  tff(c_1214, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.41/1.59  tff(c_1224, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_1214])).
% 3.41/1.59  tff(c_1230, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_1224])).
% 3.41/1.59  tff(c_1335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1230])).
% 3.41/1.59  tff(c_1336, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_1228])).
% 3.41/1.59  tff(c_1339, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_1224])).
% 3.41/1.59  tff(c_1556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1551, c_1339])).
% 3.41/1.59  tff(c_1558, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_56])).
% 3.41/1.59  tff(c_1557, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_56])).
% 3.41/1.59  tff(c_1565, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1558, c_1557])).
% 3.41/1.59  tff(c_1566, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_1565])).
% 3.41/1.59  tff(c_1568, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1566, c_1558])).
% 3.41/1.59  tff(c_1586, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1568, c_6])).
% 3.41/1.59  tff(c_1560, plain, (r1_xboole_0('#skF_11', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1558, c_14])).
% 3.41/1.59  tff(c_1567, plain, (r1_xboole_0('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1566, c_1566, c_1560])).
% 3.41/1.59  tff(c_1604, plain, (![B_304, A_305]: (~r1_xboole_0(B_304, A_305) | ~r1_tarski(B_304, A_305) | v1_xboole_0(B_304))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.41/1.59  tff(c_1607, plain, (~r1_tarski('#skF_10', '#skF_10') | v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_1567, c_1604])).
% 3.41/1.59  tff(c_1610, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1607])).
% 3.41/1.59  tff(c_1632, plain, (![A_322, B_323, D_324]: (r2_hidden('#skF_7'(A_322, B_323, k2_zfmisc_1(A_322, B_323), D_324), A_322) | ~r2_hidden(D_324, k2_zfmisc_1(A_322, B_323)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.41/1.59  tff(c_1642, plain, (![A_328, D_329, B_330]: (~v1_xboole_0(A_328) | ~r2_hidden(D_329, k2_zfmisc_1(A_328, B_330)))), inference(resolution, [status(thm)], [c_1632, c_2])).
% 3.41/1.59  tff(c_1675, plain, (![A_333, B_334]: (~v1_xboole_0(A_333) | k2_zfmisc_1(A_333, B_334)='#skF_10')), inference(resolution, [status(thm)], [c_1586, c_1642])).
% 3.41/1.59  tff(c_1692, plain, (![B_338]: (k2_zfmisc_1('#skF_10', B_338)='#skF_10')), inference(resolution, [status(thm)], [c_1610, c_1675])).
% 3.41/1.59  tff(c_1636, plain, (![A_322, D_324, B_323]: (~v1_xboole_0(A_322) | ~r2_hidden(D_324, k2_zfmisc_1(A_322, B_323)))), inference(resolution, [status(thm)], [c_1632, c_2])).
% 3.41/1.59  tff(c_1700, plain, (![D_324]: (~v1_xboole_0('#skF_10') | ~r2_hidden(D_324, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1692, c_1636])).
% 3.41/1.59  tff(c_1730, plain, (![D_339]: (~r2_hidden(D_339, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1610, c_1700])).
% 3.41/1.59  tff(c_1759, plain, (![D_340, A_341]: (~r2_hidden(D_340, k2_zfmisc_1(A_341, '#skF_10')))), inference(resolution, [status(thm)], [c_24, c_1730])).
% 3.41/1.59  tff(c_1791, plain, (![A_341]: (k2_zfmisc_1(A_341, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1586, c_1759])).
% 3.41/1.59  tff(c_54, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.41/1.59  tff(c_1578, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1568, c_1566, c_1568, c_54])).
% 3.41/1.59  tff(c_1796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1791, c_1578])).
% 3.41/1.59  tff(c_1797, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_1565])).
% 3.41/1.59  tff(c_1799, plain, (r1_xboole_0('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1797, c_1797, c_1560])).
% 3.41/1.59  tff(c_1830, plain, (![B_345, A_346]: (~r1_xboole_0(B_345, A_346) | ~r1_tarski(B_345, A_346) | v1_xboole_0(B_345))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.41/1.59  tff(c_1833, plain, (~r1_tarski('#skF_9', '#skF_9') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_1799, c_1830])).
% 3.41/1.59  tff(c_1836, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1833])).
% 3.41/1.59  tff(c_1800, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1797, c_1558])).
% 3.41/1.59  tff(c_1822, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | A_5='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1800, c_6])).
% 3.41/1.59  tff(c_1867, plain, (![A_365, B_366, D_367]: (r2_hidden('#skF_7'(A_365, B_366, k2_zfmisc_1(A_365, B_366), D_367), A_365) | ~r2_hidden(D_367, k2_zfmisc_1(A_365, B_366)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.41/1.59  tff(c_1872, plain, (![A_368, D_369, B_370]: (~v1_xboole_0(A_368) | ~r2_hidden(D_369, k2_zfmisc_1(A_368, B_370)))), inference(resolution, [status(thm)], [c_1867, c_2])).
% 3.41/1.59  tff(c_1902, plain, (![A_374, B_375]: (~v1_xboole_0(A_374) | k2_zfmisc_1(A_374, B_375)='#skF_9')), inference(resolution, [status(thm)], [c_1822, c_1872])).
% 3.41/1.59  tff(c_1905, plain, (![B_375]: (k2_zfmisc_1('#skF_9', B_375)='#skF_9')), inference(resolution, [status(thm)], [c_1836, c_1902])).
% 3.41/1.59  tff(c_1818, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1800, c_1797, c_1800, c_54])).
% 3.41/1.59  tff(c_1908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1905, c_1818])).
% 3.41/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.59  
% 3.41/1.59  Inference rules
% 3.41/1.59  ----------------------
% 3.41/1.59  #Ref     : 0
% 3.41/1.59  #Sup     : 372
% 3.41/1.59  #Fact    : 0
% 3.41/1.59  #Define  : 0
% 3.41/1.59  #Split   : 12
% 3.41/1.59  #Chain   : 0
% 3.41/1.59  #Close   : 0
% 3.41/1.59  
% 3.41/1.59  Ordering : KBO
% 3.41/1.59  
% 3.41/1.59  Simplification rules
% 3.41/1.59  ----------------------
% 3.41/1.59  #Subsume      : 95
% 3.41/1.59  #Demod        : 217
% 3.41/1.59  #Tautology    : 129
% 3.41/1.59  #SimpNegUnit  : 28
% 3.41/1.59  #BackRed      : 70
% 3.41/1.59  
% 3.41/1.59  #Partial instantiations: 0
% 3.41/1.59  #Strategies tried      : 1
% 3.41/1.59  
% 3.41/1.59  Timing (in seconds)
% 3.41/1.59  ----------------------
% 3.41/1.59  Preprocessing        : 0.32
% 3.41/1.59  Parsing              : 0.16
% 3.41/1.59  CNF conversion       : 0.03
% 3.41/1.59  Main loop            : 0.47
% 3.41/1.59  Inferencing          : 0.18
% 3.41/1.60  Reduction            : 0.13
% 3.41/1.60  Demodulation         : 0.08
% 3.41/1.60  BG Simplification    : 0.03
% 3.41/1.60  Subsumption          : 0.08
% 3.41/1.60  Abstraction          : 0.02
% 3.41/1.60  MUC search           : 0.00
% 3.41/1.60  Cooper               : 0.00
% 3.41/1.60  Total                : 0.85
% 3.41/1.60  Index Insertion      : 0.00
% 3.41/1.60  Index Deletion       : 0.00
% 3.41/1.60  Index Matching       : 0.00
% 3.41/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
