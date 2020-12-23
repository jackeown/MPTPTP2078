%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:43 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 794 expanded)
%              Number of leaves         :   30 ( 235 expanded)
%              Depth                    :   10
%              Number of atoms          :  216 (1562 expanded)
%              Number of equality atoms :   90 (1301 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_78,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_79,plain,(
    ! [A_53,B_54] : r1_xboole_0(k3_xboole_0(A_53,B_54),k5_xboole_0(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [A_10] : r1_xboole_0(k1_xboole_0,k5_xboole_0(A_10,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_79])).

tff(c_86,plain,(
    ! [A_10] : r1_xboole_0(k1_xboole_0,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_82])).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_90,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [A_10,C_58] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_58,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_100,plain,(
    ! [C_58] : ~ r2_hidden(C_58,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_74,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_210,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( r2_hidden(k4_tarski(A_76,B_77),k2_zfmisc_1(C_78,D_79))
      | ~ r2_hidden(B_77,D_79)
      | ~ r2_hidden(A_76,C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_219,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(k4_tarski(A_76,B_77),k1_xboole_0)
      | ~ r2_hidden(B_77,'#skF_12')
      | ~ r2_hidden(A_76,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_210])).

tff(c_222,plain,(
    ! [B_77,A_76] :
      ( ~ r2_hidden(B_77,'#skF_12')
      | ~ r2_hidden(A_76,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_219])).

tff(c_224,plain,(
    ! [A_80] : ~ r2_hidden(A_80,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_228,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_6,c_224])).

tff(c_232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_228])).

tff(c_234,plain,(
    ! [B_81] : ~ r2_hidden(B_81,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_238,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_6,c_234])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_238])).

tff(c_248,plain,(
    ! [A_86] : ~ r1_xboole_0(A_86,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_253,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_86,c_248])).

tff(c_254,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_256,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_260,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_256,c_10])).

tff(c_261,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_10') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_12])).

tff(c_286,plain,(
    ! [A_90,B_91] : r1_xboole_0(k3_xboole_0(A_90,B_91),k5_xboole_0(A_90,B_91)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_289,plain,(
    ! [A_11] : r1_xboole_0(k3_xboole_0(A_11,'#skF_10'),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_286])).

tff(c_293,plain,(
    ! [A_11] : r1_xboole_0('#skF_10',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_289])).

tff(c_257,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_6])).

tff(c_430,plain,(
    ! [A_120,B_121,D_122] :
      ( r2_hidden('#skF_8'(A_120,B_121,k2_zfmisc_1(A_120,B_121),D_122),B_121)
      | ~ r2_hidden(D_122,k2_zfmisc_1(A_120,B_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_297,plain,(
    ! [A_93,B_94,C_95] :
      ( ~ r1_xboole_0(A_93,B_94)
      | ~ r2_hidden(C_95,k3_xboole_0(A_93,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_304,plain,(
    ! [A_10,C_95] :
      ( ~ r1_xboole_0(A_10,'#skF_10')
      | ~ r2_hidden(C_95,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_297])).

tff(c_306,plain,(
    ! [C_95] : ~ r2_hidden(C_95,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_490,plain,(
    ! [D_126,A_127] : ~ r2_hidden(D_126,k2_zfmisc_1(A_127,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_430,c_306])).

tff(c_513,plain,(
    ! [A_127] : k2_zfmisc_1(A_127,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_257,c_490])).

tff(c_255,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_282,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_255])).

tff(c_52,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_284,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10'
    | k2_zfmisc_1('#skF_11','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_256,c_52])).

tff(c_285,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_284])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_285])).

tff(c_547,plain,(
    ! [A_131] : ~ r1_xboole_0(A_131,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_552,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_293,c_547])).

tff(c_553,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_559,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_9') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_12])).

tff(c_558,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_553,c_10])).

tff(c_585,plain,(
    ! [A_135,B_136] : r1_xboole_0(k3_xboole_0(A_135,B_136),k5_xboole_0(A_135,B_136)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_588,plain,(
    ! [A_10] : r1_xboole_0('#skF_9',k5_xboole_0(A_10,'#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_585])).

tff(c_592,plain,(
    ! [A_10] : r1_xboole_0('#skF_9',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_588])).

tff(c_555,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_6])).

tff(c_718,plain,(
    ! [A_162,B_163,D_164] :
      ( r2_hidden('#skF_7'(A_162,B_163,k2_zfmisc_1(A_162,B_163),D_164),A_162)
      | ~ r2_hidden(D_164,k2_zfmisc_1(A_162,B_163)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_596,plain,(
    ! [A_138,B_139,C_140] :
      ( ~ r1_xboole_0(A_138,B_139)
      | ~ r2_hidden(C_140,k3_xboole_0(A_138,B_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_603,plain,(
    ! [A_10,C_140] :
      ( ~ r1_xboole_0(A_10,'#skF_9')
      | ~ r2_hidden(C_140,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_596])).

tff(c_606,plain,(
    ! [C_140] : ~ r2_hidden(C_140,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_603])).

tff(c_729,plain,(
    ! [D_165,B_166] : ~ r2_hidden(D_165,k2_zfmisc_1('#skF_9',B_166)) ),
    inference(resolution,[status(thm)],[c_718,c_606])).

tff(c_744,plain,(
    ! [B_166] : k2_zfmisc_1('#skF_9',B_166) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_555,c_729])).

tff(c_581,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_255])).

tff(c_582,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_553,c_52])).

tff(c_583,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_582])).

tff(c_748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_583])).

tff(c_750,plain,(
    ! [A_167] : ~ r1_xboole_0(A_167,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_603])).

tff(c_755,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_592,c_750])).

tff(c_757,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_772,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_12') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_12])).

tff(c_771,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_757,c_10])).

tff(c_1070,plain,(
    ! [A_213,B_214] : r1_xboole_0(k3_xboole_0(A_213,B_214),k5_xboole_0(A_213,B_214)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1073,plain,(
    ! [A_10] : r1_xboole_0('#skF_12',k5_xboole_0(A_10,'#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_1070])).

tff(c_1077,plain,(
    ! [A_10] : r1_xboole_0('#skF_12',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_1073])).

tff(c_1068,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_6])).

tff(c_1256,plain,(
    ! [A_246,B_247,D_248] :
      ( r2_hidden('#skF_7'(A_246,B_247,k2_zfmisc_1(A_246,B_247),D_248),A_246)
      | ~ r2_hidden(D_248,k2_zfmisc_1(A_246,B_247)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1081,plain,(
    ! [A_216,B_217,C_218] :
      ( ~ r1_xboole_0(A_216,B_217)
      | ~ r2_hidden(C_218,k3_xboole_0(A_216,B_217)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1088,plain,(
    ! [A_10,C_218] :
      ( ~ r1_xboole_0(A_10,'#skF_12')
      | ~ r2_hidden(C_218,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_1081])).

tff(c_1092,plain,(
    ! [C_218] : ~ r2_hidden(C_218,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_1088])).

tff(c_1271,plain,(
    ! [D_249,B_250] : ~ r2_hidden(D_249,k2_zfmisc_1('#skF_12',B_250)) ),
    inference(resolution,[status(thm)],[c_1256,c_1092])).

tff(c_1294,plain,(
    ! [B_250] : k2_zfmisc_1('#skF_12',B_250) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1068,c_1271])).

tff(c_804,plain,(
    ! [A_171,B_172] : r1_xboole_0(k3_xboole_0(A_171,B_172),k5_xboole_0(A_171,B_172)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_807,plain,(
    ! [A_11] : r1_xboole_0(k3_xboole_0(A_11,'#skF_12'),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_804])).

tff(c_811,plain,(
    ! [A_11] : r1_xboole_0('#skF_12',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_807])).

tff(c_802,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_6])).

tff(c_965,plain,(
    ! [A_203,B_204,D_205] :
      ( r2_hidden('#skF_8'(A_203,B_204,k2_zfmisc_1(A_203,B_204),D_205),B_204)
      | ~ r2_hidden(D_205,k2_zfmisc_1(A_203,B_204)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_815,plain,(
    ! [A_174,B_175,C_176] :
      ( ~ r1_xboole_0(A_174,B_175)
      | ~ r2_hidden(C_176,k3_xboole_0(A_174,B_175)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_822,plain,(
    ! [A_10,C_176] :
      ( ~ r1_xboole_0(A_10,'#skF_12')
      | ~ r2_hidden(C_176,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_815])).

tff(c_824,plain,(
    ! [C_176] : ~ r2_hidden(C_176,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_822])).

tff(c_1009,plain,(
    ! [D_207,A_208] : ~ r2_hidden(D_207,k2_zfmisc_1(A_208,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_965,c_824])).

tff(c_1032,plain,(
    ! [A_208] : k2_zfmisc_1(A_208,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_802,c_1009])).

tff(c_756,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_778,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_757,c_756])).

tff(c_779,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_778])).

tff(c_44,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_758,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_758])).

tff(c_768,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_791,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_757,c_768])).

tff(c_1036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_791])).

tff(c_1038,plain,(
    ! [A_209] : ~ r1_xboole_0(A_209,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_822])).

tff(c_1043,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_811,c_1038])).

tff(c_1044,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_778])).

tff(c_1059,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1044,c_757,c_768])).

tff(c_1298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_1059])).

tff(c_1300,plain,(
    ! [A_251] : ~ r1_xboole_0(A_251,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_1088])).

tff(c_1305,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1077,c_1300])).

tff(c_1307,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1306,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1314,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_1307,c_1306])).

tff(c_1315,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1314])).

tff(c_1309,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_11') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_12])).

tff(c_1325,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_10') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1315,c_1309])).

tff(c_1308,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1307,c_1307,c_10])).

tff(c_1335,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1315,c_1315,c_1308])).

tff(c_1350,plain,(
    ! [A_255,B_256] : r1_xboole_0(k3_xboole_0(A_255,B_256),k5_xboole_0(A_255,B_256)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1353,plain,(
    ! [A_10] : r1_xboole_0('#skF_10',k5_xboole_0(A_10,'#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1335,c_1350])).

tff(c_1357,plain,(
    ! [A_10] : r1_xboole_0('#skF_10',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_1353])).

tff(c_1316,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1315,c_1307])).

tff(c_1348,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1316,c_6])).

tff(c_1485,plain,(
    ! [A_282,B_283,D_284] :
      ( r2_hidden('#skF_8'(A_282,B_283,k2_zfmisc_1(A_282,B_283),D_284),B_283)
      | ~ r2_hidden(D_284,k2_zfmisc_1(A_282,B_283)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1359,plain,(
    ! [A_257,B_258,C_259] :
      ( ~ r1_xboole_0(A_257,B_258)
      | ~ r2_hidden(C_259,k3_xboole_0(A_257,B_258)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1366,plain,(
    ! [A_10,C_259] :
      ( ~ r1_xboole_0(A_10,'#skF_10')
      | ~ r2_hidden(C_259,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1335,c_1359])).

tff(c_1370,plain,(
    ! [C_259] : ~ r2_hidden(C_259,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1366])).

tff(c_1496,plain,(
    ! [D_285,A_286] : ~ r2_hidden(D_285,k2_zfmisc_1(A_286,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_1485,c_1370])).

tff(c_1511,plain,(
    ! [A_286] : k2_zfmisc_1(A_286,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1348,c_1496])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1347,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1316,c_1315,c_1316,c_48])).

tff(c_1515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_1347])).

tff(c_1517,plain,(
    ! [A_287] : ~ r1_xboole_0(A_287,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_1366])).

tff(c_1522,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1357,c_1517])).

tff(c_1523,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1314])).

tff(c_1535,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_9') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1309])).

tff(c_1545,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1523,c_1308])).

tff(c_1561,plain,(
    ! [A_291,B_292] : r1_xboole_0(k3_xboole_0(A_291,B_292),k5_xboole_0(A_291,B_292)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1564,plain,(
    ! [A_10] : r1_xboole_0('#skF_9',k5_xboole_0(A_10,'#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1545,c_1561])).

tff(c_1568,plain,(
    ! [A_10] : r1_xboole_0('#skF_9',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_1564])).

tff(c_1525,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1307])).

tff(c_1559,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_6])).

tff(c_1780,plain,(
    ! [A_328,B_329,D_330] :
      ( r2_hidden('#skF_7'(A_328,B_329,k2_zfmisc_1(A_328,B_329),D_330),A_328)
      | ~ r2_hidden(D_330,k2_zfmisc_1(A_328,B_329)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1570,plain,(
    ! [A_293,B_294,C_295] :
      ( ~ r1_xboole_0(A_293,B_294)
      | ~ r2_hidden(C_295,k3_xboole_0(A_293,B_294)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1577,plain,(
    ! [A_10,C_295] :
      ( ~ r1_xboole_0(A_10,'#skF_9')
      | ~ r2_hidden(C_295,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1545,c_1570])).

tff(c_1581,plain,(
    ! [C_295] : ~ r2_hidden(C_295,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1577])).

tff(c_1800,plain,(
    ! [D_331,B_332] : ~ r2_hidden(D_331,k2_zfmisc_1('#skF_9',B_332)) ),
    inference(resolution,[status(thm)],[c_1780,c_1581])).

tff(c_1823,plain,(
    ! [B_332] : k2_zfmisc_1('#skF_9',B_332) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1559,c_1800])).

tff(c_1558,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_1523,c_1525,c_48])).

tff(c_1827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1823,c_1558])).

tff(c_1829,plain,(
    ! [A_333] : ~ r1_xboole_0(A_333,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1577])).

tff(c_1834,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1568,c_1829])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:51:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.49  
% 2.96/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.49  %$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12
% 2.96/1.49  
% 2.96/1.49  %Foreground sorts:
% 2.96/1.49  
% 2.96/1.49  
% 2.96/1.49  %Background operators:
% 2.96/1.49  
% 2.96/1.49  
% 2.96/1.49  %Foreground operators:
% 2.96/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.96/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.49  tff('#skF_11', type, '#skF_11': $i).
% 2.96/1.49  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.96/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.96/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.96/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.96/1.49  tff('#skF_10', type, '#skF_10': $i).
% 2.96/1.49  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.96/1.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.96/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.96/1.49  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.96/1.49  tff('#skF_9', type, '#skF_9': $i).
% 2.96/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.96/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.96/1.49  tff('#skF_12', type, '#skF_12': $i).
% 2.96/1.49  
% 2.96/1.52  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.96/1.52  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.96/1.52  tff(f_49, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 2.96/1.52  tff(f_78, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.96/1.52  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.96/1.52  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.96/1.52  tff(f_71, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.96/1.52  tff(f_65, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.96/1.52  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.96/1.52  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.52  tff(c_79, plain, (![A_53, B_54]: (r1_xboole_0(k3_xboole_0(A_53, B_54), k5_xboole_0(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.52  tff(c_82, plain, (![A_10]: (r1_xboole_0(k1_xboole_0, k5_xboole_0(A_10, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_79])).
% 2.96/1.52  tff(c_86, plain, (![A_10]: (r1_xboole_0(k1_xboole_0, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_82])).
% 2.96/1.52  tff(c_46, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.96/1.52  tff(c_72, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_46])).
% 2.96/1.52  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.52  tff(c_50, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.96/1.52  tff(c_71, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_50])).
% 2.96/1.52  tff(c_90, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.52  tff(c_97, plain, (![A_10, C_58]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_90])).
% 2.96/1.52  tff(c_100, plain, (![C_58]: (~r2_hidden(C_58, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_97])).
% 2.96/1.52  tff(c_54, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.96/1.52  tff(c_74, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 2.96/1.52  tff(c_210, plain, (![A_76, B_77, C_78, D_79]: (r2_hidden(k4_tarski(A_76, B_77), k2_zfmisc_1(C_78, D_79)) | ~r2_hidden(B_77, D_79) | ~r2_hidden(A_76, C_78))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.96/1.52  tff(c_219, plain, (![A_76, B_77]: (r2_hidden(k4_tarski(A_76, B_77), k1_xboole_0) | ~r2_hidden(B_77, '#skF_12') | ~r2_hidden(A_76, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_210])).
% 2.96/1.52  tff(c_222, plain, (![B_77, A_76]: (~r2_hidden(B_77, '#skF_12') | ~r2_hidden(A_76, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_100, c_219])).
% 2.96/1.52  tff(c_224, plain, (![A_80]: (~r2_hidden(A_80, '#skF_11'))), inference(splitLeft, [status(thm)], [c_222])).
% 2.96/1.52  tff(c_228, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_6, c_224])).
% 2.96/1.52  tff(c_232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_228])).
% 2.96/1.52  tff(c_234, plain, (![B_81]: (~r2_hidden(B_81, '#skF_12'))), inference(splitRight, [status(thm)], [c_222])).
% 2.96/1.52  tff(c_238, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_6, c_234])).
% 2.96/1.52  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_238])).
% 2.96/1.52  tff(c_248, plain, (![A_86]: (~r1_xboole_0(A_86, k1_xboole_0))), inference(splitRight, [status(thm)], [c_97])).
% 2.96/1.52  tff(c_253, plain, $false, inference(resolution, [status(thm)], [c_86, c_248])).
% 2.96/1.52  tff(c_254, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_54])).
% 2.96/1.52  tff(c_256, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_254])).
% 2.96/1.52  tff(c_260, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_256, c_10])).
% 2.96/1.52  tff(c_261, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_10')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_256, c_12])).
% 2.96/1.52  tff(c_286, plain, (![A_90, B_91]: (r1_xboole_0(k3_xboole_0(A_90, B_91), k5_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.52  tff(c_289, plain, (![A_11]: (r1_xboole_0(k3_xboole_0(A_11, '#skF_10'), A_11))), inference(superposition, [status(thm), theory('equality')], [c_261, c_286])).
% 2.96/1.52  tff(c_293, plain, (![A_11]: (r1_xboole_0('#skF_10', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_289])).
% 2.96/1.52  tff(c_257, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_6])).
% 2.96/1.52  tff(c_430, plain, (![A_120, B_121, D_122]: (r2_hidden('#skF_8'(A_120, B_121, k2_zfmisc_1(A_120, B_121), D_122), B_121) | ~r2_hidden(D_122, k2_zfmisc_1(A_120, B_121)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.96/1.52  tff(c_297, plain, (![A_93, B_94, C_95]: (~r1_xboole_0(A_93, B_94) | ~r2_hidden(C_95, k3_xboole_0(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.52  tff(c_304, plain, (![A_10, C_95]: (~r1_xboole_0(A_10, '#skF_10') | ~r2_hidden(C_95, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_260, c_297])).
% 2.96/1.52  tff(c_306, plain, (![C_95]: (~r2_hidden(C_95, '#skF_10'))), inference(splitLeft, [status(thm)], [c_304])).
% 2.96/1.52  tff(c_490, plain, (![D_126, A_127]: (~r2_hidden(D_126, k2_zfmisc_1(A_127, '#skF_10')))), inference(resolution, [status(thm)], [c_430, c_306])).
% 2.96/1.52  tff(c_513, plain, (![A_127]: (k2_zfmisc_1(A_127, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_257, c_490])).
% 2.96/1.52  tff(c_255, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.96/1.52  tff(c_282, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_256, c_255])).
% 2.96/1.52  tff(c_52, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.96/1.52  tff(c_284, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10' | k2_zfmisc_1('#skF_11', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_256, c_256, c_52])).
% 2.96/1.52  tff(c_285, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_282, c_284])).
% 2.96/1.52  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_513, c_285])).
% 2.96/1.52  tff(c_547, plain, (![A_131]: (~r1_xboole_0(A_131, '#skF_10'))), inference(splitRight, [status(thm)], [c_304])).
% 2.96/1.52  tff(c_552, plain, $false, inference(resolution, [status(thm)], [c_293, c_547])).
% 2.96/1.52  tff(c_553, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_254])).
% 2.96/1.52  tff(c_559, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_9')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_553, c_12])).
% 2.96/1.52  tff(c_558, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_553, c_553, c_10])).
% 2.96/1.52  tff(c_585, plain, (![A_135, B_136]: (r1_xboole_0(k3_xboole_0(A_135, B_136), k5_xboole_0(A_135, B_136)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.52  tff(c_588, plain, (![A_10]: (r1_xboole_0('#skF_9', k5_xboole_0(A_10, '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_558, c_585])).
% 2.96/1.52  tff(c_592, plain, (![A_10]: (r1_xboole_0('#skF_9', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_559, c_588])).
% 2.96/1.52  tff(c_555, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_553, c_6])).
% 2.96/1.52  tff(c_718, plain, (![A_162, B_163, D_164]: (r2_hidden('#skF_7'(A_162, B_163, k2_zfmisc_1(A_162, B_163), D_164), A_162) | ~r2_hidden(D_164, k2_zfmisc_1(A_162, B_163)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.96/1.52  tff(c_596, plain, (![A_138, B_139, C_140]: (~r1_xboole_0(A_138, B_139) | ~r2_hidden(C_140, k3_xboole_0(A_138, B_139)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.52  tff(c_603, plain, (![A_10, C_140]: (~r1_xboole_0(A_10, '#skF_9') | ~r2_hidden(C_140, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_558, c_596])).
% 2.96/1.52  tff(c_606, plain, (![C_140]: (~r2_hidden(C_140, '#skF_9'))), inference(splitLeft, [status(thm)], [c_603])).
% 2.96/1.52  tff(c_729, plain, (![D_165, B_166]: (~r2_hidden(D_165, k2_zfmisc_1('#skF_9', B_166)))), inference(resolution, [status(thm)], [c_718, c_606])).
% 2.96/1.52  tff(c_744, plain, (![B_166]: (k2_zfmisc_1('#skF_9', B_166)='#skF_9')), inference(resolution, [status(thm)], [c_555, c_729])).
% 2.96/1.52  tff(c_581, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_553, c_255])).
% 2.96/1.52  tff(c_582, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_553, c_553, c_52])).
% 2.96/1.52  tff(c_583, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_581, c_582])).
% 2.96/1.52  tff(c_748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_744, c_583])).
% 2.96/1.52  tff(c_750, plain, (![A_167]: (~r1_xboole_0(A_167, '#skF_9'))), inference(splitRight, [status(thm)], [c_603])).
% 2.96/1.52  tff(c_755, plain, $false, inference(resolution, [status(thm)], [c_592, c_750])).
% 2.96/1.52  tff(c_757, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_46])).
% 2.96/1.52  tff(c_772, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_12')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_757, c_12])).
% 2.96/1.52  tff(c_771, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_757, c_757, c_10])).
% 2.96/1.52  tff(c_1070, plain, (![A_213, B_214]: (r1_xboole_0(k3_xboole_0(A_213, B_214), k5_xboole_0(A_213, B_214)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.52  tff(c_1073, plain, (![A_10]: (r1_xboole_0('#skF_12', k5_xboole_0(A_10, '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_771, c_1070])).
% 2.96/1.52  tff(c_1077, plain, (![A_10]: (r1_xboole_0('#skF_12', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_772, c_1073])).
% 2.96/1.52  tff(c_1068, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_757, c_6])).
% 2.96/1.52  tff(c_1256, plain, (![A_246, B_247, D_248]: (r2_hidden('#skF_7'(A_246, B_247, k2_zfmisc_1(A_246, B_247), D_248), A_246) | ~r2_hidden(D_248, k2_zfmisc_1(A_246, B_247)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.96/1.52  tff(c_1081, plain, (![A_216, B_217, C_218]: (~r1_xboole_0(A_216, B_217) | ~r2_hidden(C_218, k3_xboole_0(A_216, B_217)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.52  tff(c_1088, plain, (![A_10, C_218]: (~r1_xboole_0(A_10, '#skF_12') | ~r2_hidden(C_218, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_771, c_1081])).
% 2.96/1.52  tff(c_1092, plain, (![C_218]: (~r2_hidden(C_218, '#skF_12'))), inference(splitLeft, [status(thm)], [c_1088])).
% 2.96/1.52  tff(c_1271, plain, (![D_249, B_250]: (~r2_hidden(D_249, k2_zfmisc_1('#skF_12', B_250)))), inference(resolution, [status(thm)], [c_1256, c_1092])).
% 2.96/1.52  tff(c_1294, plain, (![B_250]: (k2_zfmisc_1('#skF_12', B_250)='#skF_12')), inference(resolution, [status(thm)], [c_1068, c_1271])).
% 2.96/1.52  tff(c_804, plain, (![A_171, B_172]: (r1_xboole_0(k3_xboole_0(A_171, B_172), k5_xboole_0(A_171, B_172)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.52  tff(c_807, plain, (![A_11]: (r1_xboole_0(k3_xboole_0(A_11, '#skF_12'), A_11))), inference(superposition, [status(thm), theory('equality')], [c_772, c_804])).
% 2.96/1.52  tff(c_811, plain, (![A_11]: (r1_xboole_0('#skF_12', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_771, c_807])).
% 2.96/1.52  tff(c_802, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_757, c_6])).
% 2.96/1.52  tff(c_965, plain, (![A_203, B_204, D_205]: (r2_hidden('#skF_8'(A_203, B_204, k2_zfmisc_1(A_203, B_204), D_205), B_204) | ~r2_hidden(D_205, k2_zfmisc_1(A_203, B_204)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.96/1.52  tff(c_815, plain, (![A_174, B_175, C_176]: (~r1_xboole_0(A_174, B_175) | ~r2_hidden(C_176, k3_xboole_0(A_174, B_175)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.52  tff(c_822, plain, (![A_10, C_176]: (~r1_xboole_0(A_10, '#skF_12') | ~r2_hidden(C_176, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_771, c_815])).
% 2.96/1.52  tff(c_824, plain, (![C_176]: (~r2_hidden(C_176, '#skF_12'))), inference(splitLeft, [status(thm)], [c_822])).
% 2.96/1.52  tff(c_1009, plain, (![D_207, A_208]: (~r2_hidden(D_207, k2_zfmisc_1(A_208, '#skF_12')))), inference(resolution, [status(thm)], [c_965, c_824])).
% 2.96/1.52  tff(c_1032, plain, (![A_208]: (k2_zfmisc_1(A_208, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_802, c_1009])).
% 2.96/1.52  tff(c_756, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_46])).
% 2.96/1.52  tff(c_778, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_757, c_757, c_756])).
% 2.96/1.52  tff(c_779, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_778])).
% 2.96/1.52  tff(c_44, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.96/1.52  tff(c_758, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_44])).
% 2.96/1.52  tff(c_767, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_757, c_758])).
% 2.96/1.52  tff(c_768, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 2.96/1.52  tff(c_791, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_779, c_757, c_768])).
% 2.96/1.52  tff(c_1036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1032, c_791])).
% 2.96/1.52  tff(c_1038, plain, (![A_209]: (~r1_xboole_0(A_209, '#skF_12'))), inference(splitRight, [status(thm)], [c_822])).
% 2.96/1.52  tff(c_1043, plain, $false, inference(resolution, [status(thm)], [c_811, c_1038])).
% 2.96/1.52  tff(c_1044, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_778])).
% 2.96/1.52  tff(c_1059, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1044, c_757, c_768])).
% 2.96/1.52  tff(c_1298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1294, c_1059])).
% 2.96/1.52  tff(c_1300, plain, (![A_251]: (~r1_xboole_0(A_251, '#skF_12'))), inference(splitRight, [status(thm)], [c_1088])).
% 2.96/1.52  tff(c_1305, plain, $false, inference(resolution, [status(thm)], [c_1077, c_1300])).
% 2.96/1.52  tff(c_1307, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_50])).
% 2.96/1.52  tff(c_1306, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_50])).
% 2.96/1.52  tff(c_1314, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1307, c_1307, c_1306])).
% 2.96/1.52  tff(c_1315, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_1314])).
% 2.96/1.52  tff(c_1309, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_11')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_1307, c_12])).
% 2.96/1.52  tff(c_1325, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_10')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_1315, c_1309])).
% 2.96/1.52  tff(c_1308, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1307, c_1307, c_10])).
% 2.96/1.52  tff(c_1335, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1315, c_1315, c_1308])).
% 2.96/1.52  tff(c_1350, plain, (![A_255, B_256]: (r1_xboole_0(k3_xboole_0(A_255, B_256), k5_xboole_0(A_255, B_256)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.52  tff(c_1353, plain, (![A_10]: (r1_xboole_0('#skF_10', k5_xboole_0(A_10, '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_1335, c_1350])).
% 2.96/1.52  tff(c_1357, plain, (![A_10]: (r1_xboole_0('#skF_10', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_1325, c_1353])).
% 2.96/1.52  tff(c_1316, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1315, c_1307])).
% 2.96/1.52  tff(c_1348, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1316, c_6])).
% 2.96/1.52  tff(c_1485, plain, (![A_282, B_283, D_284]: (r2_hidden('#skF_8'(A_282, B_283, k2_zfmisc_1(A_282, B_283), D_284), B_283) | ~r2_hidden(D_284, k2_zfmisc_1(A_282, B_283)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.96/1.52  tff(c_1359, plain, (![A_257, B_258, C_259]: (~r1_xboole_0(A_257, B_258) | ~r2_hidden(C_259, k3_xboole_0(A_257, B_258)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.52  tff(c_1366, plain, (![A_10, C_259]: (~r1_xboole_0(A_10, '#skF_10') | ~r2_hidden(C_259, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1335, c_1359])).
% 2.96/1.52  tff(c_1370, plain, (![C_259]: (~r2_hidden(C_259, '#skF_10'))), inference(splitLeft, [status(thm)], [c_1366])).
% 2.96/1.52  tff(c_1496, plain, (![D_285, A_286]: (~r2_hidden(D_285, k2_zfmisc_1(A_286, '#skF_10')))), inference(resolution, [status(thm)], [c_1485, c_1370])).
% 2.96/1.52  tff(c_1511, plain, (![A_286]: (k2_zfmisc_1(A_286, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1348, c_1496])).
% 2.96/1.52  tff(c_48, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.96/1.52  tff(c_1347, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1316, c_1315, c_1316, c_48])).
% 2.96/1.52  tff(c_1515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1511, c_1347])).
% 2.96/1.52  tff(c_1517, plain, (![A_287]: (~r1_xboole_0(A_287, '#skF_10'))), inference(splitRight, [status(thm)], [c_1366])).
% 2.96/1.52  tff(c_1522, plain, $false, inference(resolution, [status(thm)], [c_1357, c_1517])).
% 2.96/1.52  tff(c_1523, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_1314])).
% 2.96/1.52  tff(c_1535, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_9')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1309])).
% 2.96/1.52  tff(c_1545, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1523, c_1308])).
% 2.96/1.52  tff(c_1561, plain, (![A_291, B_292]: (r1_xboole_0(k3_xboole_0(A_291, B_292), k5_xboole_0(A_291, B_292)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.52  tff(c_1564, plain, (![A_10]: (r1_xboole_0('#skF_9', k5_xboole_0(A_10, '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_1545, c_1561])).
% 2.96/1.52  tff(c_1568, plain, (![A_10]: (r1_xboole_0('#skF_9', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_1564])).
% 2.96/1.52  tff(c_1525, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1307])).
% 2.96/1.52  tff(c_1559, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_6])).
% 2.96/1.52  tff(c_1780, plain, (![A_328, B_329, D_330]: (r2_hidden('#skF_7'(A_328, B_329, k2_zfmisc_1(A_328, B_329), D_330), A_328) | ~r2_hidden(D_330, k2_zfmisc_1(A_328, B_329)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.96/1.52  tff(c_1570, plain, (![A_293, B_294, C_295]: (~r1_xboole_0(A_293, B_294) | ~r2_hidden(C_295, k3_xboole_0(A_293, B_294)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.52  tff(c_1577, plain, (![A_10, C_295]: (~r1_xboole_0(A_10, '#skF_9') | ~r2_hidden(C_295, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1545, c_1570])).
% 2.96/1.52  tff(c_1581, plain, (![C_295]: (~r2_hidden(C_295, '#skF_9'))), inference(splitLeft, [status(thm)], [c_1577])).
% 2.96/1.52  tff(c_1800, plain, (![D_331, B_332]: (~r2_hidden(D_331, k2_zfmisc_1('#skF_9', B_332)))), inference(resolution, [status(thm)], [c_1780, c_1581])).
% 2.96/1.52  tff(c_1823, plain, (![B_332]: (k2_zfmisc_1('#skF_9', B_332)='#skF_9')), inference(resolution, [status(thm)], [c_1559, c_1800])).
% 2.96/1.52  tff(c_1558, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_1523, c_1525, c_48])).
% 2.96/1.52  tff(c_1827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1823, c_1558])).
% 2.96/1.52  tff(c_1829, plain, (![A_333]: (~r1_xboole_0(A_333, '#skF_9'))), inference(splitRight, [status(thm)], [c_1577])).
% 2.96/1.52  tff(c_1834, plain, $false, inference(resolution, [status(thm)], [c_1568, c_1829])).
% 2.96/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.52  
% 2.96/1.52  Inference rules
% 2.96/1.52  ----------------------
% 2.96/1.52  #Ref     : 0
% 2.96/1.52  #Sup     : 368
% 2.96/1.52  #Fact    : 0
% 2.96/1.52  #Define  : 0
% 2.96/1.52  #Split   : 17
% 2.96/1.52  #Chain   : 0
% 2.96/1.52  #Close   : 0
% 2.96/1.52  
% 2.96/1.52  Ordering : KBO
% 2.96/1.52  
% 2.96/1.52  Simplification rules
% 2.96/1.52  ----------------------
% 2.96/1.52  #Subsume      : 74
% 2.96/1.52  #Demod        : 249
% 2.96/1.52  #Tautology    : 213
% 2.96/1.52  #SimpNegUnit  : 41
% 2.96/1.52  #BackRed      : 36
% 2.96/1.52  
% 2.96/1.52  #Partial instantiations: 0
% 2.96/1.52  #Strategies tried      : 1
% 2.96/1.52  
% 2.96/1.52  Timing (in seconds)
% 2.96/1.52  ----------------------
% 2.96/1.52  Preprocessing        : 0.31
% 2.96/1.52  Parsing              : 0.16
% 2.96/1.52  CNF conversion       : 0.03
% 2.96/1.52  Main loop            : 0.42
% 2.96/1.52  Inferencing          : 0.17
% 2.96/1.52  Reduction            : 0.13
% 2.96/1.52  Demodulation         : 0.09
% 2.96/1.52  BG Simplification    : 0.02
% 2.96/1.52  Subsumption          : 0.06
% 2.96/1.52  Abstraction          : 0.02
% 2.96/1.52  MUC search           : 0.00
% 2.96/1.52  Cooper               : 0.00
% 2.96/1.52  Total                : 0.79
% 2.96/1.52  Index Insertion      : 0.00
% 2.96/1.52  Index Deletion       : 0.00
% 2.96/1.52  Index Matching       : 0.00
% 2.96/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
