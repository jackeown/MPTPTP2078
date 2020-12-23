%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:40 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 528 expanded)
%              Number of leaves         :   26 ( 164 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 (1014 expanded)
%              Number of equality atoms :   85 ( 784 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(c_12,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,
    ( k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_53,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,
    ( k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_51,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_16,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_66,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [A_10,C_30] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_66])).

tff(c_76,plain,(
    ! [C_30] : ~ r2_hidden(C_30,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_73])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k2_zfmisc_1('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_109,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( r2_hidden(k4_tarski(A_44,B_45),k2_zfmisc_1(C_46,D_47))
      | ~ r2_hidden(B_45,D_47)
      | ~ r2_hidden(A_44,C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_118,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(k4_tarski(A_44,B_45),k1_xboole_0)
      | ~ r2_hidden(B_45,'#skF_8')
      | ~ r2_hidden(A_44,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_109])).

tff(c_121,plain,(
    ! [B_45,A_44] :
      ( ~ r2_hidden(B_45,'#skF_8')
      | ~ r2_hidden(A_44,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_118])).

tff(c_123,plain,(
    ! [A_48] : ~ r2_hidden(A_48,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_127,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_127])).

tff(c_133,plain,(
    ! [B_49] : ~ r2_hidden(B_49,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_137,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6,c_133])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_137])).

tff(c_142,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_144,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_146,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_6])).

tff(c_248,plain,(
    ! [A_84,B_85,C_86,D_87] :
      ( r2_hidden('#skF_4'(A_84,B_85,C_86,D_87),C_86)
      | ~ r2_hidden(D_87,A_84)
      | ~ r1_tarski(A_84,k2_zfmisc_1(B_85,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_149,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_16])).

tff(c_148,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_144,c_14])).

tff(c_173,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,k3_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_180,plain,(
    ! [A_10,C_57] :
      ( ~ r1_xboole_0(A_10,'#skF_6')
      | ~ r2_hidden(C_57,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_173])).

tff(c_183,plain,(
    ! [C_57] : ~ r2_hidden(C_57,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_180])).

tff(c_328,plain,(
    ! [D_96,A_97,B_98] :
      ( ~ r2_hidden(D_96,A_97)
      | ~ r1_tarski(A_97,k2_zfmisc_1(B_98,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_248,c_183])).

tff(c_344,plain,(
    ! [A_99,B_100] :
      ( ~ r1_tarski(A_99,k2_zfmisc_1(B_100,'#skF_6'))
      | A_99 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_146,c_328])).

tff(c_352,plain,(
    ! [B_100] : k2_zfmisc_1(B_100,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12,c_344])).

tff(c_38,plain,
    ( k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0
    | k2_zfmisc_1('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_155,plain,
    ( k2_zfmisc_1('#skF_5','#skF_6') != '#skF_6'
    | k2_zfmisc_1('#skF_7','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_144,c_38])).

tff(c_156,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_156])).

tff(c_358,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_143,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_144,c_143])).

tff(c_377,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_380,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_6])).

tff(c_503,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( r2_hidden('#skF_3'(A_137,B_138,C_139,D_140),B_138)
      | ~ r2_hidden(D_140,A_137)
      | ~ r1_tarski(A_137,k2_zfmisc_1(B_138,C_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_383,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_16])).

tff(c_382,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_377,c_14])).

tff(c_401,plain,(
    ! [A_105,B_106,C_107] :
      ( ~ r1_xboole_0(A_105,B_106)
      | ~ r2_hidden(C_107,k3_xboole_0(A_105,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_408,plain,(
    ! [A_10,C_107] :
      ( ~ r1_xboole_0(A_10,'#skF_5')
      | ~ r2_hidden(C_107,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_401])).

tff(c_411,plain,(
    ! [C_107] : ~ r2_hidden(C_107,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_408])).

tff(c_542,plain,(
    ! [D_144,A_145,C_146] :
      ( ~ r2_hidden(D_144,A_145)
      | ~ r1_tarski(A_145,k2_zfmisc_1('#skF_5',C_146)) ) ),
    inference(resolution,[status(thm)],[c_503,c_411])).

tff(c_558,plain,(
    ! [A_147,C_148] :
      ( ~ r1_tarski(A_147,k2_zfmisc_1('#skF_5',C_148))
      | A_147 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_380,c_542])).

tff(c_566,plain,(
    ! [C_148] : k2_zfmisc_1('#skF_5',C_148) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12,c_558])).

tff(c_389,plain,
    ( k2_zfmisc_1('#skF_5','#skF_6') != '#skF_5'
    | k2_zfmisc_1('#skF_7','#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_377,c_38])).

tff(c_390,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_390])).

tff(c_572,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_377,c_143])).

tff(c_582,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_583,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_6])).

tff(c_869,plain,(
    ! [A_227,B_228,C_229,D_230] :
      ( r2_hidden('#skF_4'(A_227,B_228,C_229,D_230),C_229)
      | ~ r2_hidden(D_230,A_227)
      | ~ r1_tarski(A_227,k2_zfmisc_1(B_228,C_229)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_586,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_16])).

tff(c_585,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_582,c_14])).

tff(c_800,plain,(
    ! [A_200,B_201,C_202] :
      ( ~ r1_xboole_0(A_200,B_201)
      | ~ r2_hidden(C_202,k3_xboole_0(A_200,B_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_807,plain,(
    ! [A_10,C_202] :
      ( ~ r1_xboole_0(A_10,'#skF_8')
      | ~ r2_hidden(C_202,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_800])).

tff(c_810,plain,(
    ! [C_202] : ~ r2_hidden(C_202,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_807])).

tff(c_955,plain,(
    ! [D_241,A_242,B_243] :
      ( ~ r2_hidden(D_241,A_242)
      | ~ r1_tarski(A_242,k2_zfmisc_1(B_243,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_869,c_810])).

tff(c_971,plain,(
    ! [A_244,B_245] :
      ( ~ r1_tarski(A_244,k2_zfmisc_1(B_245,'#skF_8'))
      | A_244 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_583,c_955])).

tff(c_979,plain,(
    ! [B_245] : k2_zfmisc_1(B_245,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_12,c_971])).

tff(c_737,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( r2_hidden('#skF_3'(A_188,B_189,C_190,D_191),B_189)
      | ~ r2_hidden(D_191,A_188)
      | ~ r1_tarski(A_188,k2_zfmisc_1(B_189,C_190)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_611,plain,(
    ! [A_153,B_154,C_155] :
      ( ~ r1_xboole_0(A_153,B_154)
      | ~ r2_hidden(C_155,k3_xboole_0(A_153,B_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_618,plain,(
    ! [A_10,C_155] :
      ( ~ r1_xboole_0(A_10,'#skF_8')
      | ~ r2_hidden(C_155,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_611])).

tff(c_621,plain,(
    ! [C_155] : ~ r2_hidden(C_155,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_618])).

tff(c_752,plain,(
    ! [D_192,A_193,C_194] :
      ( ~ r2_hidden(D_192,A_193)
      | ~ r1_tarski(A_193,k2_zfmisc_1('#skF_8',C_194)) ) ),
    inference(resolution,[status(thm)],[c_737,c_621])).

tff(c_768,plain,(
    ! [A_195,C_196] :
      ( ~ r1_tarski(A_195,k2_zfmisc_1('#skF_8',C_196))
      | A_195 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_583,c_752])).

tff(c_776,plain,(
    ! [C_196] : k2_zfmisc_1('#skF_8',C_196) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_12,c_768])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_601,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_582,c_582,c_32])).

tff(c_602,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_601])).

tff(c_581,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_599,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_581])).

tff(c_603,plain,(
    k2_zfmisc_1('#skF_8','#skF_6') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_599])).

tff(c_781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_603])).

tff(c_782,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_785,plain,(
    k2_zfmisc_1('#skF_5','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_599])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_785])).

tff(c_986,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1003,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_986,c_986,c_36])).

tff(c_1004,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1003])).

tff(c_1010,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_986])).

tff(c_1028,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_6])).

tff(c_1096,plain,(
    ! [A_277,B_278,C_279,D_280] :
      ( r2_hidden('#skF_3'(A_277,B_278,C_279,D_280),B_278)
      | ~ r2_hidden(D_280,A_277)
      | ~ r1_tarski(A_277,k2_zfmisc_1(B_278,C_279)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_988,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_16])).

tff(c_1009,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_988])).

tff(c_987,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_986,c_14])).

tff(c_1008,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_1004,c_987])).

tff(c_1040,plain,(
    ! [A_253,B_254,C_255] :
      ( ~ r1_xboole_0(A_253,B_254)
      | ~ r2_hidden(C_255,k3_xboole_0(A_253,B_254)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1047,plain,(
    ! [A_10,C_255] :
      ( ~ r1_xboole_0(A_10,'#skF_5')
      | ~ r2_hidden(C_255,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_1040])).

tff(c_1050,plain,(
    ! [C_255] : ~ r2_hidden(C_255,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_1047])).

tff(c_1195,plain,(
    ! [D_294,A_295,C_296] :
      ( ~ r2_hidden(D_294,A_295)
      | ~ r1_tarski(A_295,k2_zfmisc_1('#skF_5',C_296)) ) ),
    inference(resolution,[status(thm)],[c_1096,c_1050])).

tff(c_1211,plain,(
    ! [A_297,C_298] :
      ( ~ r1_tarski(A_297,k2_zfmisc_1('#skF_5',C_298))
      | A_297 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1028,c_1195])).

tff(c_1219,plain,(
    ! [C_298] : k2_zfmisc_1('#skF_5',C_298) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12,c_1211])).

tff(c_985,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1001,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_985])).

tff(c_1007,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_1001])).

tff(c_1224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1007])).

tff(c_1225,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1003])).

tff(c_1232,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1225,c_986])).

tff(c_1251,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1232,c_6])).

tff(c_1309,plain,(
    ! [A_324,B_325,C_326,D_327] :
      ( r2_hidden('#skF_4'(A_324,B_325,C_326,D_327),C_326)
      | ~ r2_hidden(D_327,A_324)
      | ~ r1_tarski(A_324,k2_zfmisc_1(B_325,C_326)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1231,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1225,c_988])).

tff(c_1230,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1225,c_1225,c_987])).

tff(c_1264,plain,(
    ! [A_304,B_305,C_306] :
      ( ~ r1_xboole_0(A_304,B_305)
      | ~ r2_hidden(C_306,k3_xboole_0(A_304,B_305)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1271,plain,(
    ! [A_10,C_306] :
      ( ~ r1_xboole_0(A_10,'#skF_6')
      | ~ r2_hidden(C_306,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_1264])).

tff(c_1274,plain,(
    ! [C_306] : ~ r2_hidden(C_306,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1231,c_1271])).

tff(c_1320,plain,(
    ! [D_328,A_329,B_330] :
      ( ~ r2_hidden(D_328,A_329)
      | ~ r1_tarski(A_329,k2_zfmisc_1(B_330,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1309,c_1274])).

tff(c_1333,plain,(
    ! [A_331,B_332] :
      ( ~ r1_tarski(A_331,k2_zfmisc_1(B_332,'#skF_6'))
      | A_331 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1251,c_1320])).

tff(c_1338,plain,(
    ! [B_332] : k2_zfmisc_1(B_332,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12,c_1333])).

tff(c_1229,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1225,c_1001])).

tff(c_1343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1338,c_1229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:57:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.50  
% 2.96/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 2.96/1.51  
% 2.96/1.51  %Foreground sorts:
% 2.96/1.51  
% 2.96/1.51  
% 2.96/1.51  %Background operators:
% 2.96/1.51  
% 2.96/1.51  
% 2.96/1.51  %Foreground operators:
% 2.96/1.51  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.96/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.51  tff('#skF_7', type, '#skF_7': $i).
% 2.96/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.51  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.51  tff('#skF_6', type, '#skF_6': $i).
% 2.96/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.96/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.96/1.51  tff('#skF_8', type, '#skF_8': $i).
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.96/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.96/1.51  
% 3.10/1.53  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.10/1.53  tff(f_83, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.10/1.53  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.10/1.53  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.10/1.53  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.10/1.53  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.10/1.53  tff(f_63, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.10/1.53  tff(f_76, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 3.10/1.53  tff(c_12, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.10/1.53  tff(c_30, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0 | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.10/1.53  tff(c_53, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_30])).
% 3.10/1.53  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.10/1.53  tff(c_34, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0 | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.10/1.53  tff(c_51, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_34])).
% 3.10/1.53  tff(c_16, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.10/1.53  tff(c_14, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.10/1.53  tff(c_66, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.10/1.53  tff(c_73, plain, (![A_10, C_30]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_66])).
% 3.10/1.53  tff(c_76, plain, (![C_30]: (~r2_hidden(C_30, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_73])).
% 3.10/1.53  tff(c_40, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k2_zfmisc_1('#skF_7', '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.10/1.53  tff(c_54, plain, (k2_zfmisc_1('#skF_7', '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 3.10/1.53  tff(c_109, plain, (![A_44, B_45, C_46, D_47]: (r2_hidden(k4_tarski(A_44, B_45), k2_zfmisc_1(C_46, D_47)) | ~r2_hidden(B_45, D_47) | ~r2_hidden(A_44, C_46))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.10/1.53  tff(c_118, plain, (![A_44, B_45]: (r2_hidden(k4_tarski(A_44, B_45), k1_xboole_0) | ~r2_hidden(B_45, '#skF_8') | ~r2_hidden(A_44, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_109])).
% 3.10/1.53  tff(c_121, plain, (![B_45, A_44]: (~r2_hidden(B_45, '#skF_8') | ~r2_hidden(A_44, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_76, c_118])).
% 3.10/1.53  tff(c_123, plain, (![A_48]: (~r2_hidden(A_48, '#skF_7'))), inference(splitLeft, [status(thm)], [c_121])).
% 3.10/1.53  tff(c_127, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_6, c_123])).
% 3.10/1.53  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_127])).
% 3.10/1.53  tff(c_133, plain, (![B_49]: (~r2_hidden(B_49, '#skF_8'))), inference(splitRight, [status(thm)], [c_121])).
% 3.10/1.53  tff(c_137, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_6, c_133])).
% 3.10/1.53  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_137])).
% 3.10/1.53  tff(c_142, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_40])).
% 3.10/1.53  tff(c_144, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_142])).
% 3.10/1.53  tff(c_146, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_6])).
% 3.10/1.53  tff(c_248, plain, (![A_84, B_85, C_86, D_87]: (r2_hidden('#skF_4'(A_84, B_85, C_86, D_87), C_86) | ~r2_hidden(D_87, A_84) | ~r1_tarski(A_84, k2_zfmisc_1(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.10/1.53  tff(c_149, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_16])).
% 3.10/1.53  tff(c_148, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_144, c_14])).
% 3.15/1.53  tff(c_173, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, k3_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.53  tff(c_180, plain, (![A_10, C_57]: (~r1_xboole_0(A_10, '#skF_6') | ~r2_hidden(C_57, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_173])).
% 3.15/1.53  tff(c_183, plain, (![C_57]: (~r2_hidden(C_57, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_180])).
% 3.15/1.53  tff(c_328, plain, (![D_96, A_97, B_98]: (~r2_hidden(D_96, A_97) | ~r1_tarski(A_97, k2_zfmisc_1(B_98, '#skF_6')))), inference(resolution, [status(thm)], [c_248, c_183])).
% 3.15/1.53  tff(c_344, plain, (![A_99, B_100]: (~r1_tarski(A_99, k2_zfmisc_1(B_100, '#skF_6')) | A_99='#skF_6')), inference(resolution, [status(thm)], [c_146, c_328])).
% 3.15/1.53  tff(c_352, plain, (![B_100]: (k2_zfmisc_1(B_100, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_12, c_344])).
% 3.15/1.53  tff(c_38, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0 | k2_zfmisc_1('#skF_7', '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.15/1.53  tff(c_155, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_6' | k2_zfmisc_1('#skF_7', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_144, c_38])).
% 3.15/1.53  tff(c_156, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_6'), inference(splitLeft, [status(thm)], [c_155])).
% 3.15/1.53  tff(c_357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_352, c_156])).
% 3.15/1.53  tff(c_358, plain, (k2_zfmisc_1('#skF_7', '#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_155])).
% 3.15/1.53  tff(c_143, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.15/1.53  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_358, c_144, c_143])).
% 3.15/1.53  tff(c_377, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_142])).
% 3.15/1.53  tff(c_380, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_6])).
% 3.15/1.53  tff(c_503, plain, (![A_137, B_138, C_139, D_140]: (r2_hidden('#skF_3'(A_137, B_138, C_139, D_140), B_138) | ~r2_hidden(D_140, A_137) | ~r1_tarski(A_137, k2_zfmisc_1(B_138, C_139)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.53  tff(c_383, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_377, c_16])).
% 3.15/1.53  tff(c_382, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_377, c_14])).
% 3.15/1.53  tff(c_401, plain, (![A_105, B_106, C_107]: (~r1_xboole_0(A_105, B_106) | ~r2_hidden(C_107, k3_xboole_0(A_105, B_106)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.53  tff(c_408, plain, (![A_10, C_107]: (~r1_xboole_0(A_10, '#skF_5') | ~r2_hidden(C_107, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_382, c_401])).
% 3.15/1.53  tff(c_411, plain, (![C_107]: (~r2_hidden(C_107, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_408])).
% 3.15/1.53  tff(c_542, plain, (![D_144, A_145, C_146]: (~r2_hidden(D_144, A_145) | ~r1_tarski(A_145, k2_zfmisc_1('#skF_5', C_146)))), inference(resolution, [status(thm)], [c_503, c_411])).
% 3.15/1.53  tff(c_558, plain, (![A_147, C_148]: (~r1_tarski(A_147, k2_zfmisc_1('#skF_5', C_148)) | A_147='#skF_5')), inference(resolution, [status(thm)], [c_380, c_542])).
% 3.15/1.53  tff(c_566, plain, (![C_148]: (k2_zfmisc_1('#skF_5', C_148)='#skF_5')), inference(resolution, [status(thm)], [c_12, c_558])).
% 3.15/1.53  tff(c_389, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_5' | k2_zfmisc_1('#skF_7', '#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_377, c_377, c_38])).
% 3.15/1.53  tff(c_390, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_5'), inference(splitLeft, [status(thm)], [c_389])).
% 3.15/1.53  tff(c_571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_566, c_390])).
% 3.15/1.53  tff(c_572, plain, (k2_zfmisc_1('#skF_7', '#skF_8')='#skF_5'), inference(splitRight, [status(thm)], [c_389])).
% 3.15/1.53  tff(c_580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_572, c_377, c_143])).
% 3.15/1.53  tff(c_582, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_30])).
% 3.15/1.53  tff(c_583, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_582, c_6])).
% 3.15/1.53  tff(c_869, plain, (![A_227, B_228, C_229, D_230]: (r2_hidden('#skF_4'(A_227, B_228, C_229, D_230), C_229) | ~r2_hidden(D_230, A_227) | ~r1_tarski(A_227, k2_zfmisc_1(B_228, C_229)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.53  tff(c_586, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_582, c_16])).
% 3.15/1.53  tff(c_585, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_582, c_582, c_14])).
% 3.15/1.53  tff(c_800, plain, (![A_200, B_201, C_202]: (~r1_xboole_0(A_200, B_201) | ~r2_hidden(C_202, k3_xboole_0(A_200, B_201)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.53  tff(c_807, plain, (![A_10, C_202]: (~r1_xboole_0(A_10, '#skF_8') | ~r2_hidden(C_202, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_585, c_800])).
% 3.15/1.53  tff(c_810, plain, (![C_202]: (~r2_hidden(C_202, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_807])).
% 3.15/1.53  tff(c_955, plain, (![D_241, A_242, B_243]: (~r2_hidden(D_241, A_242) | ~r1_tarski(A_242, k2_zfmisc_1(B_243, '#skF_8')))), inference(resolution, [status(thm)], [c_869, c_810])).
% 3.15/1.53  tff(c_971, plain, (![A_244, B_245]: (~r1_tarski(A_244, k2_zfmisc_1(B_245, '#skF_8')) | A_244='#skF_8')), inference(resolution, [status(thm)], [c_583, c_955])).
% 3.15/1.53  tff(c_979, plain, (![B_245]: (k2_zfmisc_1(B_245, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_12, c_971])).
% 3.15/1.53  tff(c_737, plain, (![A_188, B_189, C_190, D_191]: (r2_hidden('#skF_3'(A_188, B_189, C_190, D_191), B_189) | ~r2_hidden(D_191, A_188) | ~r1_tarski(A_188, k2_zfmisc_1(B_189, C_190)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.53  tff(c_611, plain, (![A_153, B_154, C_155]: (~r1_xboole_0(A_153, B_154) | ~r2_hidden(C_155, k3_xboole_0(A_153, B_154)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.53  tff(c_618, plain, (![A_10, C_155]: (~r1_xboole_0(A_10, '#skF_8') | ~r2_hidden(C_155, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_585, c_611])).
% 3.15/1.53  tff(c_621, plain, (![C_155]: (~r2_hidden(C_155, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_618])).
% 3.15/1.53  tff(c_752, plain, (![D_192, A_193, C_194]: (~r2_hidden(D_192, A_193) | ~r1_tarski(A_193, k2_zfmisc_1('#skF_8', C_194)))), inference(resolution, [status(thm)], [c_737, c_621])).
% 3.15/1.53  tff(c_768, plain, (![A_195, C_196]: (~r1_tarski(A_195, k2_zfmisc_1('#skF_8', C_196)) | A_195='#skF_8')), inference(resolution, [status(thm)], [c_583, c_752])).
% 3.15/1.53  tff(c_776, plain, (![C_196]: (k2_zfmisc_1('#skF_8', C_196)='#skF_8')), inference(resolution, [status(thm)], [c_12, c_768])).
% 3.15/1.53  tff(c_32, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.15/1.53  tff(c_601, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_582, c_582, c_582, c_32])).
% 3.15/1.53  tff(c_602, plain, ('#skF_5'='#skF_8'), inference(splitLeft, [status(thm)], [c_601])).
% 3.15/1.53  tff(c_581, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 3.15/1.53  tff(c_599, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_582, c_581])).
% 3.15/1.53  tff(c_603, plain, (k2_zfmisc_1('#skF_8', '#skF_6')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_602, c_599])).
% 3.15/1.53  tff(c_781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_776, c_603])).
% 3.15/1.53  tff(c_782, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_601])).
% 3.15/1.53  tff(c_785, plain, (k2_zfmisc_1('#skF_5', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_782, c_599])).
% 3.15/1.53  tff(c_984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_979, c_785])).
% 3.15/1.53  tff(c_986, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_34])).
% 3.15/1.53  tff(c_36, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.15/1.53  tff(c_1003, plain, ('#skF_7'='#skF_6' | '#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_986, c_986, c_986, c_36])).
% 3.15/1.53  tff(c_1004, plain, ('#skF_7'='#skF_5'), inference(splitLeft, [status(thm)], [c_1003])).
% 3.15/1.53  tff(c_1010, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_986])).
% 3.15/1.53  tff(c_1028, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_6])).
% 3.15/1.53  tff(c_1096, plain, (![A_277, B_278, C_279, D_280]: (r2_hidden('#skF_3'(A_277, B_278, C_279, D_280), B_278) | ~r2_hidden(D_280, A_277) | ~r1_tarski(A_277, k2_zfmisc_1(B_278, C_279)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.53  tff(c_988, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_986, c_16])).
% 3.15/1.53  tff(c_1009, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_988])).
% 3.15/1.53  tff(c_987, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_986, c_986, c_14])).
% 3.15/1.53  tff(c_1008, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_1004, c_987])).
% 3.15/1.53  tff(c_1040, plain, (![A_253, B_254, C_255]: (~r1_xboole_0(A_253, B_254) | ~r2_hidden(C_255, k3_xboole_0(A_253, B_254)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.53  tff(c_1047, plain, (![A_10, C_255]: (~r1_xboole_0(A_10, '#skF_5') | ~r2_hidden(C_255, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1008, c_1040])).
% 3.15/1.53  tff(c_1050, plain, (![C_255]: (~r2_hidden(C_255, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_1047])).
% 3.15/1.53  tff(c_1195, plain, (![D_294, A_295, C_296]: (~r2_hidden(D_294, A_295) | ~r1_tarski(A_295, k2_zfmisc_1('#skF_5', C_296)))), inference(resolution, [status(thm)], [c_1096, c_1050])).
% 3.15/1.53  tff(c_1211, plain, (![A_297, C_298]: (~r1_tarski(A_297, k2_zfmisc_1('#skF_5', C_298)) | A_297='#skF_5')), inference(resolution, [status(thm)], [c_1028, c_1195])).
% 3.15/1.53  tff(c_1219, plain, (![C_298]: (k2_zfmisc_1('#skF_5', C_298)='#skF_5')), inference(resolution, [status(thm)], [c_12, c_1211])).
% 3.15/1.53  tff(c_985, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.15/1.53  tff(c_1001, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_986, c_985])).
% 3.15/1.53  tff(c_1007, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_1001])).
% 3.15/1.53  tff(c_1224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1007])).
% 3.15/1.53  tff(c_1225, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_1003])).
% 3.15/1.53  tff(c_1232, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1225, c_986])).
% 3.15/1.53  tff(c_1251, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1232, c_6])).
% 3.15/1.53  tff(c_1309, plain, (![A_324, B_325, C_326, D_327]: (r2_hidden('#skF_4'(A_324, B_325, C_326, D_327), C_326) | ~r2_hidden(D_327, A_324) | ~r1_tarski(A_324, k2_zfmisc_1(B_325, C_326)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.15/1.53  tff(c_1231, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1225, c_988])).
% 3.15/1.53  tff(c_1230, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1225, c_1225, c_987])).
% 3.15/1.53  tff(c_1264, plain, (![A_304, B_305, C_306]: (~r1_xboole_0(A_304, B_305) | ~r2_hidden(C_306, k3_xboole_0(A_304, B_305)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.53  tff(c_1271, plain, (![A_10, C_306]: (~r1_xboole_0(A_10, '#skF_6') | ~r2_hidden(C_306, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1230, c_1264])).
% 3.15/1.53  tff(c_1274, plain, (![C_306]: (~r2_hidden(C_306, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1231, c_1271])).
% 3.15/1.53  tff(c_1320, plain, (![D_328, A_329, B_330]: (~r2_hidden(D_328, A_329) | ~r1_tarski(A_329, k2_zfmisc_1(B_330, '#skF_6')))), inference(resolution, [status(thm)], [c_1309, c_1274])).
% 3.15/1.53  tff(c_1333, plain, (![A_331, B_332]: (~r1_tarski(A_331, k2_zfmisc_1(B_332, '#skF_6')) | A_331='#skF_6')), inference(resolution, [status(thm)], [c_1251, c_1320])).
% 3.15/1.53  tff(c_1338, plain, (![B_332]: (k2_zfmisc_1(B_332, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_12, c_1333])).
% 3.15/1.53  tff(c_1229, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1225, c_1001])).
% 3.15/1.53  tff(c_1343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1338, c_1229])).
% 3.15/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.53  
% 3.15/1.53  Inference rules
% 3.15/1.53  ----------------------
% 3.15/1.53  #Ref     : 0
% 3.15/1.53  #Sup     : 272
% 3.15/1.53  #Fact    : 0
% 3.15/1.53  #Define  : 0
% 3.15/1.53  #Split   : 11
% 3.15/1.53  #Chain   : 0
% 3.15/1.53  #Close   : 0
% 3.15/1.53  
% 3.15/1.53  Ordering : KBO
% 3.15/1.53  
% 3.15/1.53  Simplification rules
% 3.15/1.53  ----------------------
% 3.15/1.53  #Subsume      : 45
% 3.15/1.53  #Demod        : 151
% 3.15/1.53  #Tautology    : 120
% 3.15/1.53  #SimpNegUnit  : 22
% 3.15/1.53  #BackRed      : 54
% 3.15/1.53  
% 3.15/1.53  #Partial instantiations: 0
% 3.15/1.53  #Strategies tried      : 1
% 3.15/1.53  
% 3.15/1.53  Timing (in seconds)
% 3.15/1.53  ----------------------
% 3.15/1.53  Preprocessing        : 0.30
% 3.15/1.53  Parsing              : 0.16
% 3.15/1.53  CNF conversion       : 0.02
% 3.15/1.54  Main loop            : 0.44
% 3.15/1.54  Inferencing          : 0.18
% 3.15/1.54  Reduction            : 0.12
% 3.15/1.54  Demodulation         : 0.08
% 3.15/1.54  BG Simplification    : 0.02
% 3.15/1.54  Subsumption          : 0.08
% 3.15/1.54  Abstraction          : 0.02
% 3.15/1.54  MUC search           : 0.00
% 3.15/1.54  Cooper               : 0.00
% 3.15/1.54  Total                : 0.79
% 3.15/1.54  Index Insertion      : 0.00
% 3.15/1.54  Index Deletion       : 0.00
% 3.15/1.54  Index Matching       : 0.00
% 3.15/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
