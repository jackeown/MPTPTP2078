%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:45 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 739 expanded)
%              Number of leaves         :   26 ( 222 expanded)
%              Depth                    :   12
%              Number of atoms          :  282 (1621 expanded)
%              Number of equality atoms :   88 ( 953 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_439,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_504,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( r2_hidden(k4_tarski(A_188,B_189),k2_zfmisc_1(C_190,D_191))
      | ~ r2_hidden(B_189,D_191)
      | ~ r2_hidden(A_188,C_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_516,plain,(
    ! [A_188,B_189] :
      ( r2_hidden(k4_tarski(A_188,B_189),k1_xboole_0)
      | ~ r2_hidden(B_189,'#skF_12')
      | ~ r2_hidden(A_188,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_504])).

tff(c_520,plain,(
    ! [A_194,B_195] :
      ( r2_hidden(k4_tarski(A_194,B_195),k1_xboole_0)
      | ~ r2_hidden(B_195,'#skF_12')
      | ~ r2_hidden(A_194,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_504])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_451,plain,(
    ! [A_166,B_167,C_168] :
      ( ~ r1_xboole_0(A_166,B_167)
      | ~ r2_hidden(C_168,B_167)
      | ~ r2_hidden(C_168,A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_454,plain,(
    ! [C_168,A_8] :
      ( ~ r2_hidden(C_168,k1_xboole_0)
      | ~ r2_hidden(C_168,A_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_451])).

tff(c_987,plain,(
    ! [A_242,B_243,A_244] :
      ( ~ r2_hidden(k4_tarski(A_242,B_243),A_244)
      | ~ r2_hidden(B_243,'#skF_12')
      | ~ r2_hidden(A_242,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_520,c_454])).

tff(c_1008,plain,(
    ! [B_189,A_188] :
      ( ~ r2_hidden(B_189,'#skF_12')
      | ~ r2_hidden(A_188,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_516,c_987])).

tff(c_1014,plain,(
    ! [A_245] : ~ r2_hidden(A_245,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_1008])).

tff(c_1040,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_8,c_1014])).

tff(c_1049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1040])).

tff(c_1050,plain,(
    ! [B_189] : ~ r2_hidden(B_189,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_1008])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_58,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_111,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( r2_hidden(k4_tarski(A_73,B_74),k2_zfmisc_1(C_75,D_76))
      | ~ r2_hidden(B_74,D_76)
      | ~ r2_hidden(A_73,C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_120,plain,(
    ! [A_73,B_74] :
      ( r2_hidden(k4_tarski(A_73,B_74),k1_xboole_0)
      | ~ r2_hidden(B_74,'#skF_12')
      | ~ r2_hidden(A_73,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_111])).

tff(c_123,plain,(
    ! [A_77,B_78] :
      ( r2_hidden(k4_tarski(A_77,B_78),k1_xboole_0)
      | ~ r2_hidden(B_78,'#skF_12')
      | ~ r2_hidden(A_77,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_111])).

tff(c_65,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r1_xboole_0(A_53,B_54)
      | ~ r2_hidden(C_55,B_54)
      | ~ r2_hidden(C_55,A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [C_55,A_8] :
      ( ~ r2_hidden(C_55,k1_xboole_0)
      | ~ r2_hidden(C_55,A_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_65])).

tff(c_145,plain,(
    ! [A_83,B_84,A_85] :
      ( ~ r2_hidden(k4_tarski(A_83,B_84),A_85)
      | ~ r2_hidden(B_84,'#skF_12')
      | ~ r2_hidden(A_83,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_123,c_68])).

tff(c_152,plain,(
    ! [B_74,A_73] :
      ( ~ r2_hidden(B_74,'#skF_12')
      | ~ r2_hidden(A_73,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_120,c_145])).

tff(c_157,plain,(
    ! [A_86] : ~ r2_hidden(A_86,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_173,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_8,c_157])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_173])).

tff(c_183,plain,(
    ! [B_87] : ~ r2_hidden(B_87,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_199,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_8,c_183])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_199])).

tff(c_207,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_209,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_211,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_8])).

tff(c_16,plain,(
    ! [A_9,B_10,D_36] :
      ( r2_hidden('#skF_8'(A_9,B_10,k2_zfmisc_1(A_9,B_10),D_36),B_10)
      | ~ r2_hidden(D_36,k2_zfmisc_1(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_271,plain,(
    ! [A_114,B_115,D_116] :
      ( r2_hidden('#skF_8'(A_114,B_115,k2_zfmisc_1(A_114,B_115),D_116),B_115)
      | ~ r2_hidden(D_116,k2_zfmisc_1(A_114,B_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_214,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_10])).

tff(c_224,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r1_xboole_0(A_94,B_95)
      | ~ r2_hidden(C_96,B_95)
      | ~ r2_hidden(C_96,A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_227,plain,(
    ! [C_96,A_8] :
      ( ~ r2_hidden(C_96,'#skF_10')
      | ~ r2_hidden(C_96,A_8) ) ),
    inference(resolution,[status(thm)],[c_214,c_224])).

tff(c_281,plain,(
    ! [A_120,D_121,A_122] :
      ( ~ r2_hidden('#skF_8'(A_120,'#skF_10',k2_zfmisc_1(A_120,'#skF_10'),D_121),A_122)
      | ~ r2_hidden(D_121,k2_zfmisc_1(A_120,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_271,c_227])).

tff(c_287,plain,(
    ! [D_123,A_124] : ~ r2_hidden(D_123,k2_zfmisc_1(A_124,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_16,c_281])).

tff(c_316,plain,(
    ! [A_124] : k2_zfmisc_1(A_124,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_211,c_287])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_57,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_210,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_57])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_210])).

tff(c_322,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_326,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_8])).

tff(c_18,plain,(
    ! [A_9,B_10,D_36] :
      ( r2_hidden('#skF_7'(A_9,B_10,k2_zfmisc_1(A_9,B_10),D_36),A_9)
      | ~ r2_hidden(D_36,k2_zfmisc_1(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_386,plain,(
    ! [A_151,B_152,D_153] :
      ( r2_hidden('#skF_7'(A_151,B_152,k2_zfmisc_1(A_151,B_152),D_153),A_151)
      | ~ r2_hidden(D_153,k2_zfmisc_1(A_151,B_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_329,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_10])).

tff(c_339,plain,(
    ! [A_131,B_132,C_133] :
      ( ~ r1_xboole_0(A_131,B_132)
      | ~ r2_hidden(C_133,B_132)
      | ~ r2_hidden(C_133,A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_342,plain,(
    ! [C_133,A_8] :
      ( ~ r2_hidden(C_133,'#skF_9')
      | ~ r2_hidden(C_133,A_8) ) ),
    inference(resolution,[status(thm)],[c_329,c_339])).

tff(c_396,plain,(
    ! [B_157,D_158,A_159] :
      ( ~ r2_hidden('#skF_7'('#skF_9',B_157,k2_zfmisc_1('#skF_9',B_157),D_158),A_159)
      | ~ r2_hidden(D_158,k2_zfmisc_1('#skF_9',B_157)) ) ),
    inference(resolution,[status(thm)],[c_386,c_342])).

tff(c_402,plain,(
    ! [D_160,B_161] : ~ r2_hidden(D_160,k2_zfmisc_1('#skF_9',B_161)) ),
    inference(resolution,[status(thm)],[c_18,c_396])).

tff(c_432,plain,(
    ! [B_161] : k2_zfmisc_1('#skF_9',B_161) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_326,c_402])).

tff(c_325,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_57])).

tff(c_436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_325])).

tff(c_438,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_643,plain,(
    ! [A_207,B_208] :
      ( r2_hidden(k4_tarski(A_207,B_208),k1_xboole_0)
      | ~ r2_hidden(B_208,'#skF_10')
      | ~ r2_hidden(A_207,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_504])).

tff(c_496,plain,(
    ! [B_182,D_183,A_184,C_185] :
      ( r2_hidden(B_182,D_183)
      | ~ r2_hidden(k4_tarski(A_184,B_182),k2_zfmisc_1(C_185,D_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_502,plain,(
    ! [B_182,A_184] :
      ( r2_hidden(B_182,'#skF_12')
      | ~ r2_hidden(k4_tarski(A_184,B_182),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_496])).

tff(c_659,plain,(
    ! [B_208,A_207] :
      ( r2_hidden(B_208,'#skF_12')
      | ~ r2_hidden(B_208,'#skF_10')
      | ~ r2_hidden(A_207,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_643,c_502])).

tff(c_663,plain,(
    ! [A_207] : ~ r2_hidden(A_207,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_659])).

tff(c_486,plain,(
    ! [A_174,C_175,B_176,D_177] :
      ( r2_hidden(A_174,C_175)
      | ~ r2_hidden(k4_tarski(A_174,B_176),k2_zfmisc_1(C_175,D_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_489,plain,(
    ! [A_174,B_176] :
      ( r2_hidden(A_174,'#skF_9')
      | ~ r2_hidden(k4_tarski(A_174,B_176),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_486])).

tff(c_537,plain,(
    ! [A_194,B_195] :
      ( r2_hidden(A_194,'#skF_9')
      | ~ r2_hidden(B_195,'#skF_12')
      | ~ r2_hidden(A_194,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_520,c_489])).

tff(c_585,plain,(
    ! [B_200] : ~ r2_hidden(B_200,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_537])).

tff(c_597,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_8,c_585])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_597])).

tff(c_605,plain,(
    ! [A_201] :
      ( r2_hidden(A_201,'#skF_9')
      | ~ r2_hidden(A_201,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_537])).

tff(c_617,plain,
    ( r2_hidden('#skF_2'('#skF_11'),'#skF_9')
    | k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_8,c_605])).

tff(c_622,plain,(
    r2_hidden('#skF_2'('#skF_11'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_617])).

tff(c_669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_663,c_622])).

tff(c_671,plain,(
    ! [B_209] :
      ( r2_hidden(B_209,'#skF_12')
      | ~ r2_hidden(B_209,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_695,plain,
    ( r2_hidden('#skF_2'('#skF_10'),'#skF_12')
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_8,c_671])).

tff(c_696,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_695])).

tff(c_708,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_55])).

tff(c_707,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_8])).

tff(c_499,plain,(
    ! [B_182,A_184] :
      ( r2_hidden(B_182,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_184,B_182),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_496])).

tff(c_535,plain,(
    ! [B_195,A_194] :
      ( r2_hidden(B_195,'#skF_10')
      | ~ r2_hidden(B_195,'#skF_12')
      | ~ r2_hidden(A_194,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_520,c_499])).

tff(c_562,plain,(
    ! [A_198] : ~ r2_hidden(A_198,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_535])).

tff(c_574,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_8,c_562])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_574])).

tff(c_581,plain,(
    ! [B_195] :
      ( r2_hidden(B_195,'#skF_10')
      | ~ r2_hidden(B_195,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_776,plain,(
    ! [C_215,A_216] :
      ( ~ r2_hidden(C_215,'#skF_10')
      | ~ r2_hidden(C_215,A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_454])).

tff(c_837,plain,(
    ! [B_221,A_222] :
      ( ~ r2_hidden(B_221,A_222)
      | ~ r2_hidden(B_221,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_581,c_776])).

tff(c_879,plain,(
    ! [A_225] :
      ( ~ r2_hidden('#skF_2'(A_225),'#skF_12')
      | A_225 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_707,c_837])).

tff(c_883,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_707,c_879])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_708,c_708,c_883])).

tff(c_888,plain,(
    r2_hidden('#skF_2'('#skF_10'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_695])).

tff(c_1081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1050,c_888])).

tff(c_1082,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1092,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1082])).

tff(c_1083,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1104,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_1083])).

tff(c_437,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1094,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_437])).

tff(c_1109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1104,c_1094])).

tff(c_1110,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1082])).

tff(c_1113,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_437])).

tff(c_1133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1113,c_1110,c_1083])).

tff(c_1135,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1390,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1135,c_8])).

tff(c_1444,plain,(
    ! [A_323,B_324,D_325] :
      ( r2_hidden('#skF_7'(A_323,B_324,k2_zfmisc_1(A_323,B_324),D_325),A_323)
      | ~ r2_hidden(D_325,k2_zfmisc_1(A_323,B_324)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1137,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1135,c_10])).

tff(c_1397,plain,(
    ! [A_303,B_304,C_305] :
      ( ~ r1_xboole_0(A_303,B_304)
      | ~ r2_hidden(C_305,B_304)
      | ~ r2_hidden(C_305,A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1400,plain,(
    ! [C_305,A_8] :
      ( ~ r2_hidden(C_305,'#skF_12')
      | ~ r2_hidden(C_305,A_8) ) ),
    inference(resolution,[status(thm)],[c_1137,c_1397])).

tff(c_1459,plain,(
    ! [B_332,D_333,A_334] :
      ( ~ r2_hidden('#skF_7'('#skF_12',B_332,k2_zfmisc_1('#skF_12',B_332),D_333),A_334)
      | ~ r2_hidden(D_333,k2_zfmisc_1('#skF_12',B_332)) ) ),
    inference(resolution,[status(thm)],[c_1444,c_1400])).

tff(c_1465,plain,(
    ! [D_335,B_336] : ~ r2_hidden(D_335,k2_zfmisc_1('#skF_12',B_336)) ),
    inference(resolution,[status(thm)],[c_18,c_1459])).

tff(c_1500,plain,(
    ! [B_336] : k2_zfmisc_1('#skF_12',B_336) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1390,c_1465])).

tff(c_1151,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1135,c_8])).

tff(c_1204,plain,(
    ! [A_277,B_278,D_279] :
      ( r2_hidden('#skF_7'(A_277,B_278,k2_zfmisc_1(A_277,B_278),D_279),A_277)
      | ~ r2_hidden(D_279,k2_zfmisc_1(A_277,B_278)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1157,plain,(
    ! [A_257,B_258,C_259] :
      ( ~ r1_xboole_0(A_257,B_258)
      | ~ r2_hidden(C_259,B_258)
      | ~ r2_hidden(C_259,A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1160,plain,(
    ! [C_259,A_8] :
      ( ~ r2_hidden(C_259,'#skF_12')
      | ~ r2_hidden(C_259,A_8) ) ),
    inference(resolution,[status(thm)],[c_1137,c_1157])).

tff(c_1214,plain,(
    ! [B_283,D_284,A_285] :
      ( ~ r2_hidden('#skF_7'('#skF_12',B_283,k2_zfmisc_1('#skF_12',B_283),D_284),A_285)
      | ~ r2_hidden(D_284,k2_zfmisc_1('#skF_12',B_283)) ) ),
    inference(resolution,[status(thm)],[c_1204,c_1160])).

tff(c_1220,plain,(
    ! [D_286,B_287] : ~ r2_hidden(D_286,k2_zfmisc_1('#skF_12',B_287)) ),
    inference(resolution,[status(thm)],[c_18,c_1214])).

tff(c_1250,plain,(
    ! [B_287] : k2_zfmisc_1('#skF_12',B_287) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1151,c_1220])).

tff(c_1219,plain,(
    ! [D_36,B_10] : ~ r2_hidden(D_36,k2_zfmisc_1('#skF_12',B_10)) ),
    inference(resolution,[status(thm)],[c_18,c_1214])).

tff(c_1276,plain,(
    ! [D_289] : ~ r2_hidden(D_289,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_1219])).

tff(c_1316,plain,(
    ! [D_293,A_294] : ~ r2_hidden(D_293,k2_zfmisc_1(A_294,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_16,c_1276])).

tff(c_1359,plain,(
    ! [A_294] : k2_zfmisc_1(A_294,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1151,c_1316])).

tff(c_1134,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1143,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1135,c_1135,c_1134])).

tff(c_1144,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_1143])).

tff(c_42,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1150,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1135,c_1144,c_1135,c_42])).

tff(c_1381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_1150])).

tff(c_1382,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_1143])).

tff(c_1389,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1135,c_1382,c_1135,c_42])).

tff(c_1504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1500,c_1389])).

tff(c_1506,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1505,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1513,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1506,c_1506,c_1505])).

tff(c_1514,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1513])).

tff(c_1516,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1514,c_1506])).

tff(c_1531,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_8])).

tff(c_1584,plain,(
    ! [A_364,B_365,D_366] :
      ( r2_hidden('#skF_8'(A_364,B_365,k2_zfmisc_1(A_364,B_365),D_366),B_365)
      | ~ r2_hidden(D_366,k2_zfmisc_1(A_364,B_365)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1507,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1506,c_10])).

tff(c_1515,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1514,c_1507])).

tff(c_1537,plain,(
    ! [A_344,B_345,C_346] :
      ( ~ r1_xboole_0(A_344,B_345)
      | ~ r2_hidden(C_346,B_345)
      | ~ r2_hidden(C_346,A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1540,plain,(
    ! [C_346,A_8] :
      ( ~ r2_hidden(C_346,'#skF_10')
      | ~ r2_hidden(C_346,A_8) ) ),
    inference(resolution,[status(thm)],[c_1515,c_1537])).

tff(c_1594,plain,(
    ! [A_370,D_371,A_372] :
      ( ~ r2_hidden('#skF_8'(A_370,'#skF_10',k2_zfmisc_1(A_370,'#skF_10'),D_371),A_372)
      | ~ r2_hidden(D_371,k2_zfmisc_1(A_370,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1584,c_1540])).

tff(c_1606,plain,(
    ! [D_376,A_377] : ~ r2_hidden(D_376,k2_zfmisc_1(A_377,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_16,c_1594])).

tff(c_1646,plain,(
    ! [A_377] : k2_zfmisc_1(A_377,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1531,c_1606])).

tff(c_46,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1530,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_1514,c_1516,c_46])).

tff(c_1650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1646,c_1530])).

tff(c_1651,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1513])).

tff(c_1654,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1651,c_1506])).

tff(c_1671,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1654,c_8])).

tff(c_1725,plain,(
    ! [A_404,B_405,D_406] :
      ( r2_hidden('#skF_7'(A_404,B_405,k2_zfmisc_1(A_404,B_405),D_406),A_404)
      | ~ r2_hidden(D_406,k2_zfmisc_1(A_404,B_405)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1653,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1651,c_1507])).

tff(c_1678,plain,(
    ! [A_384,B_385,C_386] :
      ( ~ r1_xboole_0(A_384,B_385)
      | ~ r2_hidden(C_386,B_385)
      | ~ r2_hidden(C_386,A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1681,plain,(
    ! [C_386,A_8] :
      ( ~ r2_hidden(C_386,'#skF_9')
      | ~ r2_hidden(C_386,A_8) ) ),
    inference(resolution,[status(thm)],[c_1653,c_1678])).

tff(c_1740,plain,(
    ! [B_413,D_414,A_415] :
      ( ~ r2_hidden('#skF_7'('#skF_9',B_413,k2_zfmisc_1('#skF_9',B_413),D_414),A_415)
      | ~ r2_hidden(D_414,k2_zfmisc_1('#skF_9',B_413)) ) ),
    inference(resolution,[status(thm)],[c_1725,c_1681])).

tff(c_1746,plain,(
    ! [D_416,B_417] : ~ r2_hidden(D_416,k2_zfmisc_1('#skF_9',B_417)) ),
    inference(resolution,[status(thm)],[c_18,c_1740])).

tff(c_1781,plain,(
    ! [B_417] : k2_zfmisc_1('#skF_9',B_417) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1671,c_1746])).

tff(c_1670,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1654,c_1651,c_1654,c_46])).

tff(c_1785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_1670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:28:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.56  
% 3.18/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.56  %$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12
% 3.18/1.56  
% 3.18/1.56  %Foreground sorts:
% 3.18/1.56  
% 3.18/1.56  
% 3.18/1.56  %Background operators:
% 3.18/1.56  
% 3.18/1.56  
% 3.18/1.56  %Foreground operators:
% 3.18/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.18/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.56  tff('#skF_11', type, '#skF_11': $i).
% 3.18/1.56  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.18/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.18/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.18/1.56  tff('#skF_10', type, '#skF_10': $i).
% 3.18/1.56  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.18/1.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.18/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.18/1.56  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.18/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.18/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.18/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.18/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.18/1.56  tff('#skF_12', type, '#skF_12': $i).
% 3.18/1.56  
% 3.18/1.59  tff(f_78, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.18/1.59  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.18/1.59  tff(f_71, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.18/1.59  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.18/1.59  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.18/1.59  tff(f_65, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.18/1.59  tff(c_48, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.59  tff(c_54, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_48])).
% 3.18/1.59  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.59  tff(c_52, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.59  tff(c_439, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.18/1.59  tff(c_504, plain, (![A_188, B_189, C_190, D_191]: (r2_hidden(k4_tarski(A_188, B_189), k2_zfmisc_1(C_190, D_191)) | ~r2_hidden(B_189, D_191) | ~r2_hidden(A_188, C_190))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.18/1.59  tff(c_516, plain, (![A_188, B_189]: (r2_hidden(k4_tarski(A_188, B_189), k1_xboole_0) | ~r2_hidden(B_189, '#skF_12') | ~r2_hidden(A_188, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_439, c_504])).
% 3.18/1.59  tff(c_520, plain, (![A_194, B_195]: (r2_hidden(k4_tarski(A_194, B_195), k1_xboole_0) | ~r2_hidden(B_195, '#skF_12') | ~r2_hidden(A_194, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_439, c_504])).
% 3.18/1.59  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.18/1.59  tff(c_451, plain, (![A_166, B_167, C_168]: (~r1_xboole_0(A_166, B_167) | ~r2_hidden(C_168, B_167) | ~r2_hidden(C_168, A_166))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.59  tff(c_454, plain, (![C_168, A_8]: (~r2_hidden(C_168, k1_xboole_0) | ~r2_hidden(C_168, A_8))), inference(resolution, [status(thm)], [c_10, c_451])).
% 3.18/1.59  tff(c_987, plain, (![A_242, B_243, A_244]: (~r2_hidden(k4_tarski(A_242, B_243), A_244) | ~r2_hidden(B_243, '#skF_12') | ~r2_hidden(A_242, '#skF_11'))), inference(resolution, [status(thm)], [c_520, c_454])).
% 3.18/1.59  tff(c_1008, plain, (![B_189, A_188]: (~r2_hidden(B_189, '#skF_12') | ~r2_hidden(A_188, '#skF_11'))), inference(resolution, [status(thm)], [c_516, c_987])).
% 3.18/1.59  tff(c_1014, plain, (![A_245]: (~r2_hidden(A_245, '#skF_11'))), inference(splitLeft, [status(thm)], [c_1008])).
% 3.18/1.59  tff(c_1040, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_8, c_1014])).
% 3.18/1.59  tff(c_1049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1040])).
% 3.18/1.59  tff(c_1050, plain, (![B_189]: (~r2_hidden(B_189, '#skF_12'))), inference(splitRight, [status(thm)], [c_1008])).
% 3.18/1.59  tff(c_44, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.59  tff(c_55, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_44])).
% 3.18/1.59  tff(c_58, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.18/1.59  tff(c_111, plain, (![A_73, B_74, C_75, D_76]: (r2_hidden(k4_tarski(A_73, B_74), k2_zfmisc_1(C_75, D_76)) | ~r2_hidden(B_74, D_76) | ~r2_hidden(A_73, C_75))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.18/1.59  tff(c_120, plain, (![A_73, B_74]: (r2_hidden(k4_tarski(A_73, B_74), k1_xboole_0) | ~r2_hidden(B_74, '#skF_12') | ~r2_hidden(A_73, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_111])).
% 3.18/1.59  tff(c_123, plain, (![A_77, B_78]: (r2_hidden(k4_tarski(A_77, B_78), k1_xboole_0) | ~r2_hidden(B_78, '#skF_12') | ~r2_hidden(A_77, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_111])).
% 3.18/1.59  tff(c_65, plain, (![A_53, B_54, C_55]: (~r1_xboole_0(A_53, B_54) | ~r2_hidden(C_55, B_54) | ~r2_hidden(C_55, A_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.59  tff(c_68, plain, (![C_55, A_8]: (~r2_hidden(C_55, k1_xboole_0) | ~r2_hidden(C_55, A_8))), inference(resolution, [status(thm)], [c_10, c_65])).
% 3.18/1.59  tff(c_145, plain, (![A_83, B_84, A_85]: (~r2_hidden(k4_tarski(A_83, B_84), A_85) | ~r2_hidden(B_84, '#skF_12') | ~r2_hidden(A_83, '#skF_11'))), inference(resolution, [status(thm)], [c_123, c_68])).
% 3.18/1.59  tff(c_152, plain, (![B_74, A_73]: (~r2_hidden(B_74, '#skF_12') | ~r2_hidden(A_73, '#skF_11'))), inference(resolution, [status(thm)], [c_120, c_145])).
% 3.18/1.59  tff(c_157, plain, (![A_86]: (~r2_hidden(A_86, '#skF_11'))), inference(splitLeft, [status(thm)], [c_152])).
% 3.18/1.59  tff(c_173, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_8, c_157])).
% 3.18/1.59  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_173])).
% 3.18/1.59  tff(c_183, plain, (![B_87]: (~r2_hidden(B_87, '#skF_12'))), inference(splitRight, [status(thm)], [c_152])).
% 3.18/1.59  tff(c_199, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_8, c_183])).
% 3.18/1.59  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_199])).
% 3.18/1.59  tff(c_207, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_52])).
% 3.18/1.59  tff(c_209, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_207])).
% 3.18/1.59  tff(c_211, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_8])).
% 3.18/1.59  tff(c_16, plain, (![A_9, B_10, D_36]: (r2_hidden('#skF_8'(A_9, B_10, k2_zfmisc_1(A_9, B_10), D_36), B_10) | ~r2_hidden(D_36, k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.18/1.59  tff(c_271, plain, (![A_114, B_115, D_116]: (r2_hidden('#skF_8'(A_114, B_115, k2_zfmisc_1(A_114, B_115), D_116), B_115) | ~r2_hidden(D_116, k2_zfmisc_1(A_114, B_115)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.18/1.59  tff(c_214, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_10])).
% 3.18/1.59  tff(c_224, plain, (![A_94, B_95, C_96]: (~r1_xboole_0(A_94, B_95) | ~r2_hidden(C_96, B_95) | ~r2_hidden(C_96, A_94))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.59  tff(c_227, plain, (![C_96, A_8]: (~r2_hidden(C_96, '#skF_10') | ~r2_hidden(C_96, A_8))), inference(resolution, [status(thm)], [c_214, c_224])).
% 3.18/1.59  tff(c_281, plain, (![A_120, D_121, A_122]: (~r2_hidden('#skF_8'(A_120, '#skF_10', k2_zfmisc_1(A_120, '#skF_10'), D_121), A_122) | ~r2_hidden(D_121, k2_zfmisc_1(A_120, '#skF_10')))), inference(resolution, [status(thm)], [c_271, c_227])).
% 3.18/1.59  tff(c_287, plain, (![D_123, A_124]: (~r2_hidden(D_123, k2_zfmisc_1(A_124, '#skF_10')))), inference(resolution, [status(thm)], [c_16, c_281])).
% 3.18/1.59  tff(c_316, plain, (![A_124]: (k2_zfmisc_1(A_124, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_211, c_287])).
% 3.18/1.59  tff(c_50, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.59  tff(c_57, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 3.18/1.59  tff(c_210, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_209, c_57])).
% 3.18/1.59  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_316, c_210])).
% 3.18/1.59  tff(c_322, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_207])).
% 3.18/1.59  tff(c_326, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_8])).
% 3.18/1.59  tff(c_18, plain, (![A_9, B_10, D_36]: (r2_hidden('#skF_7'(A_9, B_10, k2_zfmisc_1(A_9, B_10), D_36), A_9) | ~r2_hidden(D_36, k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.18/1.59  tff(c_386, plain, (![A_151, B_152, D_153]: (r2_hidden('#skF_7'(A_151, B_152, k2_zfmisc_1(A_151, B_152), D_153), A_151) | ~r2_hidden(D_153, k2_zfmisc_1(A_151, B_152)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.18/1.59  tff(c_329, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_10])).
% 3.18/1.59  tff(c_339, plain, (![A_131, B_132, C_133]: (~r1_xboole_0(A_131, B_132) | ~r2_hidden(C_133, B_132) | ~r2_hidden(C_133, A_131))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.59  tff(c_342, plain, (![C_133, A_8]: (~r2_hidden(C_133, '#skF_9') | ~r2_hidden(C_133, A_8))), inference(resolution, [status(thm)], [c_329, c_339])).
% 3.18/1.59  tff(c_396, plain, (![B_157, D_158, A_159]: (~r2_hidden('#skF_7'('#skF_9', B_157, k2_zfmisc_1('#skF_9', B_157), D_158), A_159) | ~r2_hidden(D_158, k2_zfmisc_1('#skF_9', B_157)))), inference(resolution, [status(thm)], [c_386, c_342])).
% 3.18/1.59  tff(c_402, plain, (![D_160, B_161]: (~r2_hidden(D_160, k2_zfmisc_1('#skF_9', B_161)))), inference(resolution, [status(thm)], [c_18, c_396])).
% 3.18/1.59  tff(c_432, plain, (![B_161]: (k2_zfmisc_1('#skF_9', B_161)='#skF_9')), inference(resolution, [status(thm)], [c_326, c_402])).
% 3.18/1.59  tff(c_325, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_57])).
% 3.18/1.59  tff(c_436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_432, c_325])).
% 3.18/1.59  tff(c_438, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.18/1.59  tff(c_643, plain, (![A_207, B_208]: (r2_hidden(k4_tarski(A_207, B_208), k1_xboole_0) | ~r2_hidden(B_208, '#skF_10') | ~r2_hidden(A_207, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_438, c_504])).
% 3.18/1.59  tff(c_496, plain, (![B_182, D_183, A_184, C_185]: (r2_hidden(B_182, D_183) | ~r2_hidden(k4_tarski(A_184, B_182), k2_zfmisc_1(C_185, D_183)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.18/1.59  tff(c_502, plain, (![B_182, A_184]: (r2_hidden(B_182, '#skF_12') | ~r2_hidden(k4_tarski(A_184, B_182), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_439, c_496])).
% 3.18/1.59  tff(c_659, plain, (![B_208, A_207]: (r2_hidden(B_208, '#skF_12') | ~r2_hidden(B_208, '#skF_10') | ~r2_hidden(A_207, '#skF_9'))), inference(resolution, [status(thm)], [c_643, c_502])).
% 3.18/1.59  tff(c_663, plain, (![A_207]: (~r2_hidden(A_207, '#skF_9'))), inference(splitLeft, [status(thm)], [c_659])).
% 3.18/1.59  tff(c_486, plain, (![A_174, C_175, B_176, D_177]: (r2_hidden(A_174, C_175) | ~r2_hidden(k4_tarski(A_174, B_176), k2_zfmisc_1(C_175, D_177)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.18/1.59  tff(c_489, plain, (![A_174, B_176]: (r2_hidden(A_174, '#skF_9') | ~r2_hidden(k4_tarski(A_174, B_176), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_438, c_486])).
% 3.18/1.59  tff(c_537, plain, (![A_194, B_195]: (r2_hidden(A_194, '#skF_9') | ~r2_hidden(B_195, '#skF_12') | ~r2_hidden(A_194, '#skF_11'))), inference(resolution, [status(thm)], [c_520, c_489])).
% 3.18/1.59  tff(c_585, plain, (![B_200]: (~r2_hidden(B_200, '#skF_12'))), inference(splitLeft, [status(thm)], [c_537])).
% 3.18/1.59  tff(c_597, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_8, c_585])).
% 3.18/1.59  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_597])).
% 3.18/1.59  tff(c_605, plain, (![A_201]: (r2_hidden(A_201, '#skF_9') | ~r2_hidden(A_201, '#skF_11'))), inference(splitRight, [status(thm)], [c_537])).
% 3.18/1.59  tff(c_617, plain, (r2_hidden('#skF_2'('#skF_11'), '#skF_9') | k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_8, c_605])).
% 3.18/1.59  tff(c_622, plain, (r2_hidden('#skF_2'('#skF_11'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_54, c_617])).
% 3.18/1.59  tff(c_669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_663, c_622])).
% 3.18/1.59  tff(c_671, plain, (![B_209]: (r2_hidden(B_209, '#skF_12') | ~r2_hidden(B_209, '#skF_10'))), inference(splitRight, [status(thm)], [c_659])).
% 3.18/1.59  tff(c_695, plain, (r2_hidden('#skF_2'('#skF_10'), '#skF_12') | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_8, c_671])).
% 3.18/1.59  tff(c_696, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_695])).
% 3.18/1.59  tff(c_708, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_696, c_55])).
% 3.18/1.59  tff(c_707, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_696, c_8])).
% 3.18/1.59  tff(c_499, plain, (![B_182, A_184]: (r2_hidden(B_182, '#skF_10') | ~r2_hidden(k4_tarski(A_184, B_182), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_438, c_496])).
% 3.18/1.59  tff(c_535, plain, (![B_195, A_194]: (r2_hidden(B_195, '#skF_10') | ~r2_hidden(B_195, '#skF_12') | ~r2_hidden(A_194, '#skF_11'))), inference(resolution, [status(thm)], [c_520, c_499])).
% 3.18/1.59  tff(c_562, plain, (![A_198]: (~r2_hidden(A_198, '#skF_11'))), inference(splitLeft, [status(thm)], [c_535])).
% 3.18/1.59  tff(c_574, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_8, c_562])).
% 3.18/1.59  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_574])).
% 3.18/1.59  tff(c_581, plain, (![B_195]: (r2_hidden(B_195, '#skF_10') | ~r2_hidden(B_195, '#skF_12'))), inference(splitRight, [status(thm)], [c_535])).
% 3.18/1.59  tff(c_776, plain, (![C_215, A_216]: (~r2_hidden(C_215, '#skF_10') | ~r2_hidden(C_215, A_216))), inference(demodulation, [status(thm), theory('equality')], [c_696, c_454])).
% 3.18/1.59  tff(c_837, plain, (![B_221, A_222]: (~r2_hidden(B_221, A_222) | ~r2_hidden(B_221, '#skF_12'))), inference(resolution, [status(thm)], [c_581, c_776])).
% 3.18/1.59  tff(c_879, plain, (![A_225]: (~r2_hidden('#skF_2'(A_225), '#skF_12') | A_225='#skF_10')), inference(resolution, [status(thm)], [c_707, c_837])).
% 3.18/1.59  tff(c_883, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_707, c_879])).
% 3.18/1.59  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_708, c_708, c_883])).
% 3.18/1.59  tff(c_888, plain, (r2_hidden('#skF_2'('#skF_10'), '#skF_12')), inference(splitRight, [status(thm)], [c_695])).
% 3.18/1.59  tff(c_1081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1050, c_888])).
% 3.18/1.59  tff(c_1082, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_52])).
% 3.18/1.59  tff(c_1092, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_1082])).
% 3.18/1.59  tff(c_1083, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.18/1.59  tff(c_1104, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_1083])).
% 3.18/1.59  tff(c_437, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.18/1.59  tff(c_1094, plain, (k2_zfmisc_1('#skF_11', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_437])).
% 3.18/1.59  tff(c_1109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1104, c_1094])).
% 3.18/1.59  tff(c_1110, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1082])).
% 3.18/1.59  tff(c_1113, plain, (k2_zfmisc_1('#skF_11', '#skF_12')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1110, c_437])).
% 3.18/1.59  tff(c_1133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1113, c_1110, c_1083])).
% 3.18/1.59  tff(c_1135, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_44])).
% 3.18/1.59  tff(c_1390, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1135, c_8])).
% 3.18/1.59  tff(c_1444, plain, (![A_323, B_324, D_325]: (r2_hidden('#skF_7'(A_323, B_324, k2_zfmisc_1(A_323, B_324), D_325), A_323) | ~r2_hidden(D_325, k2_zfmisc_1(A_323, B_324)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.18/1.59  tff(c_1137, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_1135, c_10])).
% 3.18/1.59  tff(c_1397, plain, (![A_303, B_304, C_305]: (~r1_xboole_0(A_303, B_304) | ~r2_hidden(C_305, B_304) | ~r2_hidden(C_305, A_303))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.59  tff(c_1400, plain, (![C_305, A_8]: (~r2_hidden(C_305, '#skF_12') | ~r2_hidden(C_305, A_8))), inference(resolution, [status(thm)], [c_1137, c_1397])).
% 3.18/1.59  tff(c_1459, plain, (![B_332, D_333, A_334]: (~r2_hidden('#skF_7'('#skF_12', B_332, k2_zfmisc_1('#skF_12', B_332), D_333), A_334) | ~r2_hidden(D_333, k2_zfmisc_1('#skF_12', B_332)))), inference(resolution, [status(thm)], [c_1444, c_1400])).
% 3.18/1.59  tff(c_1465, plain, (![D_335, B_336]: (~r2_hidden(D_335, k2_zfmisc_1('#skF_12', B_336)))), inference(resolution, [status(thm)], [c_18, c_1459])).
% 3.18/1.59  tff(c_1500, plain, (![B_336]: (k2_zfmisc_1('#skF_12', B_336)='#skF_12')), inference(resolution, [status(thm)], [c_1390, c_1465])).
% 3.18/1.59  tff(c_1151, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1135, c_8])).
% 3.18/1.59  tff(c_1204, plain, (![A_277, B_278, D_279]: (r2_hidden('#skF_7'(A_277, B_278, k2_zfmisc_1(A_277, B_278), D_279), A_277) | ~r2_hidden(D_279, k2_zfmisc_1(A_277, B_278)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.18/1.59  tff(c_1157, plain, (![A_257, B_258, C_259]: (~r1_xboole_0(A_257, B_258) | ~r2_hidden(C_259, B_258) | ~r2_hidden(C_259, A_257))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.59  tff(c_1160, plain, (![C_259, A_8]: (~r2_hidden(C_259, '#skF_12') | ~r2_hidden(C_259, A_8))), inference(resolution, [status(thm)], [c_1137, c_1157])).
% 3.18/1.59  tff(c_1214, plain, (![B_283, D_284, A_285]: (~r2_hidden('#skF_7'('#skF_12', B_283, k2_zfmisc_1('#skF_12', B_283), D_284), A_285) | ~r2_hidden(D_284, k2_zfmisc_1('#skF_12', B_283)))), inference(resolution, [status(thm)], [c_1204, c_1160])).
% 3.18/1.59  tff(c_1220, plain, (![D_286, B_287]: (~r2_hidden(D_286, k2_zfmisc_1('#skF_12', B_287)))), inference(resolution, [status(thm)], [c_18, c_1214])).
% 3.18/1.59  tff(c_1250, plain, (![B_287]: (k2_zfmisc_1('#skF_12', B_287)='#skF_12')), inference(resolution, [status(thm)], [c_1151, c_1220])).
% 3.18/1.59  tff(c_1219, plain, (![D_36, B_10]: (~r2_hidden(D_36, k2_zfmisc_1('#skF_12', B_10)))), inference(resolution, [status(thm)], [c_18, c_1214])).
% 3.18/1.59  tff(c_1276, plain, (![D_289]: (~r2_hidden(D_289, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_1250, c_1219])).
% 3.18/1.59  tff(c_1316, plain, (![D_293, A_294]: (~r2_hidden(D_293, k2_zfmisc_1(A_294, '#skF_12')))), inference(resolution, [status(thm)], [c_16, c_1276])).
% 3.18/1.59  tff(c_1359, plain, (![A_294]: (k2_zfmisc_1(A_294, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_1151, c_1316])).
% 3.18/1.59  tff(c_1134, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_44])).
% 3.18/1.59  tff(c_1143, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1135, c_1135, c_1134])).
% 3.18/1.59  tff(c_1144, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_1143])).
% 3.18/1.59  tff(c_42, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.59  tff(c_1150, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1135, c_1144, c_1135, c_42])).
% 3.18/1.59  tff(c_1381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1359, c_1150])).
% 3.18/1.59  tff(c_1382, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_1143])).
% 3.18/1.59  tff(c_1389, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1135, c_1382, c_1135, c_42])).
% 3.18/1.59  tff(c_1504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1500, c_1389])).
% 3.18/1.59  tff(c_1506, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_48])).
% 3.18/1.59  tff(c_1505, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_48])).
% 3.18/1.59  tff(c_1513, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1506, c_1506, c_1505])).
% 3.18/1.59  tff(c_1514, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_1513])).
% 3.18/1.59  tff(c_1516, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1514, c_1506])).
% 3.18/1.59  tff(c_1531, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_8])).
% 3.18/1.59  tff(c_1584, plain, (![A_364, B_365, D_366]: (r2_hidden('#skF_8'(A_364, B_365, k2_zfmisc_1(A_364, B_365), D_366), B_365) | ~r2_hidden(D_366, k2_zfmisc_1(A_364, B_365)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.18/1.59  tff(c_1507, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1506, c_10])).
% 3.18/1.59  tff(c_1515, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1514, c_1507])).
% 3.18/1.59  tff(c_1537, plain, (![A_344, B_345, C_346]: (~r1_xboole_0(A_344, B_345) | ~r2_hidden(C_346, B_345) | ~r2_hidden(C_346, A_344))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.59  tff(c_1540, plain, (![C_346, A_8]: (~r2_hidden(C_346, '#skF_10') | ~r2_hidden(C_346, A_8))), inference(resolution, [status(thm)], [c_1515, c_1537])).
% 3.18/1.59  tff(c_1594, plain, (![A_370, D_371, A_372]: (~r2_hidden('#skF_8'(A_370, '#skF_10', k2_zfmisc_1(A_370, '#skF_10'), D_371), A_372) | ~r2_hidden(D_371, k2_zfmisc_1(A_370, '#skF_10')))), inference(resolution, [status(thm)], [c_1584, c_1540])).
% 3.18/1.59  tff(c_1606, plain, (![D_376, A_377]: (~r2_hidden(D_376, k2_zfmisc_1(A_377, '#skF_10')))), inference(resolution, [status(thm)], [c_16, c_1594])).
% 3.18/1.59  tff(c_1646, plain, (![A_377]: (k2_zfmisc_1(A_377, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1531, c_1606])).
% 3.18/1.59  tff(c_46, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.59  tff(c_1530, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_1514, c_1516, c_46])).
% 3.18/1.59  tff(c_1650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1646, c_1530])).
% 3.18/1.59  tff(c_1651, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_1513])).
% 3.18/1.59  tff(c_1654, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1651, c_1506])).
% 3.18/1.59  tff(c_1671, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1654, c_8])).
% 3.18/1.59  tff(c_1725, plain, (![A_404, B_405, D_406]: (r2_hidden('#skF_7'(A_404, B_405, k2_zfmisc_1(A_404, B_405), D_406), A_404) | ~r2_hidden(D_406, k2_zfmisc_1(A_404, B_405)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.18/1.59  tff(c_1653, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1651, c_1507])).
% 3.18/1.59  tff(c_1678, plain, (![A_384, B_385, C_386]: (~r1_xboole_0(A_384, B_385) | ~r2_hidden(C_386, B_385) | ~r2_hidden(C_386, A_384))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.59  tff(c_1681, plain, (![C_386, A_8]: (~r2_hidden(C_386, '#skF_9') | ~r2_hidden(C_386, A_8))), inference(resolution, [status(thm)], [c_1653, c_1678])).
% 3.18/1.59  tff(c_1740, plain, (![B_413, D_414, A_415]: (~r2_hidden('#skF_7'('#skF_9', B_413, k2_zfmisc_1('#skF_9', B_413), D_414), A_415) | ~r2_hidden(D_414, k2_zfmisc_1('#skF_9', B_413)))), inference(resolution, [status(thm)], [c_1725, c_1681])).
% 3.18/1.59  tff(c_1746, plain, (![D_416, B_417]: (~r2_hidden(D_416, k2_zfmisc_1('#skF_9', B_417)))), inference(resolution, [status(thm)], [c_18, c_1740])).
% 3.18/1.59  tff(c_1781, plain, (![B_417]: (k2_zfmisc_1('#skF_9', B_417)='#skF_9')), inference(resolution, [status(thm)], [c_1671, c_1746])).
% 3.18/1.59  tff(c_1670, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1654, c_1651, c_1654, c_46])).
% 3.18/1.59  tff(c_1785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1781, c_1670])).
% 3.18/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.59  
% 3.18/1.59  Inference rules
% 3.18/1.59  ----------------------
% 3.18/1.59  #Ref     : 0
% 3.18/1.59  #Sup     : 332
% 3.18/1.59  #Fact    : 0
% 3.18/1.59  #Define  : 0
% 3.18/1.59  #Split   : 18
% 3.18/1.59  #Chain   : 0
% 3.18/1.59  #Close   : 0
% 3.18/1.59  
% 3.18/1.59  Ordering : KBO
% 3.18/1.59  
% 3.18/1.59  Simplification rules
% 3.18/1.59  ----------------------
% 3.18/1.59  #Subsume      : 53
% 3.18/1.59  #Demod        : 168
% 3.18/1.59  #Tautology    : 122
% 3.18/1.59  #SimpNegUnit  : 35
% 3.18/1.59  #BackRed      : 79
% 3.18/1.59  
% 3.18/1.59  #Partial instantiations: 0
% 3.18/1.59  #Strategies tried      : 1
% 3.18/1.59  
% 3.18/1.59  Timing (in seconds)
% 3.18/1.59  ----------------------
% 3.18/1.59  Preprocessing        : 0.31
% 3.18/1.59  Parsing              : 0.15
% 3.18/1.59  CNF conversion       : 0.03
% 3.18/1.59  Main loop            : 0.47
% 3.18/1.59  Inferencing          : 0.19
% 3.18/1.59  Reduction            : 0.12
% 3.18/1.59  Demodulation         : 0.08
% 3.18/1.59  BG Simplification    : 0.03
% 3.18/1.59  Subsumption          : 0.08
% 3.18/1.59  Abstraction          : 0.02
% 3.18/1.59  MUC search           : 0.00
% 3.18/1.59  Cooper               : 0.00
% 3.18/1.59  Total                : 0.84
% 3.18/1.59  Index Insertion      : 0.00
% 3.18/1.59  Index Deletion       : 0.00
% 3.18/1.59  Index Matching       : 0.00
% 3.18/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
