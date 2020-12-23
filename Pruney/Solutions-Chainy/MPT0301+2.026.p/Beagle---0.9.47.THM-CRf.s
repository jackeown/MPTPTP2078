%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:43 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 462 expanded)
%              Number of leaves         :   27 ( 146 expanded)
%              Depth                    :    9
%              Number of atoms          :  171 ( 897 expanded)
%              Number of equality atoms :   80 ( 660 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_1042,plain,(
    ! [A_258,B_259] :
      ( r2_hidden('#skF_1'(A_258,B_259),B_259)
      | r2_hidden('#skF_2'(A_258,B_259),A_258)
      | B_259 = A_258 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_847,plain,(
    ! [A_222,B_223] :
      ( r2_hidden('#skF_1'(A_222,B_223),B_223)
      | r2_hidden('#skF_2'(A_222,B_223),A_222)
      | B_223 = A_222 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_715,plain,(
    ! [A_190,B_191] :
      ( r2_hidden('#skF_1'(A_190,B_191),B_191)
      | r2_hidden('#skF_2'(A_190,B_191),A_190)
      | B_191 = A_190 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_393,plain,(
    ! [A_120,B_121] :
      ( r2_hidden('#skF_1'(A_120,B_121),B_121)
      | r2_hidden('#skF_2'(A_120,B_121),A_120)
      | B_121 = A_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_93,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_1'(A_63,B_64),B_64)
      | r2_hidden('#skF_2'(A_63,B_64),A_63)
      | B_64 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,B_47)
      | ~ r1_xboole_0(k1_tarski(A_46),B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_63,plain,(
    ! [A_46] : ~ r2_hidden(A_46,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_58])).

tff(c_107,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_64),B_64)
      | k1_xboole_0 = B_64 ) ),
    inference(resolution,[status(thm)],[c_93,c_63])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_65,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_119,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( r2_hidden(k4_tarski(A_66,B_67),k2_zfmisc_1(C_68,D_69))
      | ~ r2_hidden(B_67,D_69)
      | ~ r2_hidden(A_66,C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_128,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(k4_tarski(A_66,B_67),k1_xboole_0)
      | ~ r2_hidden(B_67,'#skF_12')
      | ~ r2_hidden(A_66,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_119])).

tff(c_131,plain,(
    ! [B_67,A_66] :
      ( ~ r2_hidden(B_67,'#skF_12')
      | ~ r2_hidden(A_66,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_128])).

tff(c_133,plain,(
    ! [A_70] : ~ r2_hidden(A_70,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_137,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_107,c_133])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_137])).

tff(c_153,plain,(
    ! [B_71] : ~ r2_hidden(B_71,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_157,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_107,c_153])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_157])).

tff(c_172,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_174,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_173,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_361,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_173])).

tff(c_197,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),B_87)
      | r2_hidden('#skF_2'(A_86,B_87),A_86)
      | B_87 = A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [A_46] : ~ r2_hidden(A_46,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_63])).

tff(c_211,plain,(
    ! [B_87] :
      ( r2_hidden('#skF_1'('#skF_10',B_87),B_87)
      | B_87 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_197,c_175])).

tff(c_306,plain,(
    ! [A_101,B_102,D_103] :
      ( r2_hidden('#skF_8'(A_101,B_102,k2_zfmisc_1(A_101,B_102),D_103),B_102)
      | ~ r2_hidden(D_103,k2_zfmisc_1(A_101,B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_316,plain,(
    ! [D_104,A_105] : ~ r2_hidden(D_104,k2_zfmisc_1(A_105,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_306,c_175])).

tff(c_352,plain,(
    ! [A_105] : k2_zfmisc_1(A_105,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_211,c_316])).

tff(c_52,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_190,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10'
    | k2_zfmisc_1('#skF_11','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_174,c_52])).

tff(c_191,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_191])).

tff(c_359,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_359])).

tff(c_363,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_365,plain,(
    ! [A_46] : ~ r2_hidden(A_46,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_63])).

tff(c_401,plain,(
    ! [B_121] :
      ( r2_hidden('#skF_1'('#skF_9',B_121),B_121)
      | B_121 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_393,c_365])).

tff(c_435,plain,(
    ! [A_129,B_130,D_131] :
      ( r2_hidden('#skF_7'(A_129,B_130,k2_zfmisc_1(A_129,B_130),D_131),A_129)
      | ~ r2_hidden(D_131,k2_zfmisc_1(A_129,B_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_447,plain,(
    ! [D_135,B_136] : ~ r2_hidden(D_135,k2_zfmisc_1('#skF_9',B_136)) ),
    inference(resolution,[status(thm)],[c_435,c_365])).

tff(c_479,plain,(
    ! [B_136] : k2_zfmisc_1('#skF_9',B_136) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_401,c_447])).

tff(c_381,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_173])).

tff(c_382,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_363,c_52])).

tff(c_383,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_382])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_383])).

tff(c_488,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_490,plain,(
    ! [A_4] : r1_xboole_0(A_4,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_10])).

tff(c_689,plain,(
    ! [A_173,B_174] :
      ( ~ r2_hidden(A_173,B_174)
      | ~ r1_xboole_0(k1_tarski(A_173),B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_694,plain,(
    ! [A_173] : ~ r2_hidden(A_173,'#skF_12') ),
    inference(resolution,[status(thm)],[c_490,c_689])).

tff(c_729,plain,(
    ! [B_191] :
      ( r2_hidden('#skF_1'('#skF_12',B_191),B_191)
      | B_191 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_715,c_694])).

tff(c_750,plain,(
    ! [A_197,B_198,D_199] :
      ( r2_hidden('#skF_7'(A_197,B_198,k2_zfmisc_1(A_197,B_198),D_199),A_197)
      | ~ r2_hidden(D_199,k2_zfmisc_1(A_197,B_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_762,plain,(
    ! [D_203,B_204] : ~ r2_hidden(D_203,k2_zfmisc_1('#skF_12',B_204)) ),
    inference(resolution,[status(thm)],[c_750,c_694])).

tff(c_794,plain,(
    ! [B_204] : k2_zfmisc_1('#skF_12',B_204) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_729,c_762])).

tff(c_529,plain,(
    ! [A_153,B_154] :
      ( r2_hidden('#skF_1'(A_153,B_154),B_154)
      | r2_hidden('#skF_2'(A_153,B_154),A_153)
      | B_154 = A_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_506,plain,(
    ! [A_138,B_139] :
      ( ~ r2_hidden(A_138,B_139)
      | ~ r1_xboole_0(k1_tarski(A_138),B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_511,plain,(
    ! [A_138] : ~ r2_hidden(A_138,'#skF_12') ),
    inference(resolution,[status(thm)],[c_490,c_506])).

tff(c_542,plain,(
    ! [B_154] :
      ( r2_hidden('#skF_1'('#skF_12',B_154),B_154)
      | B_154 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_529,c_511])).

tff(c_627,plain,(
    ! [A_168,B_169,D_170] :
      ( r2_hidden('#skF_8'(A_168,B_169,k2_zfmisc_1(A_168,B_169),D_170),B_169)
      | ~ r2_hidden(D_170,k2_zfmisc_1(A_168,B_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_637,plain,(
    ! [D_171,A_172] : ~ r2_hidden(D_171,k2_zfmisc_1(A_172,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_627,c_511])).

tff(c_672,plain,(
    ! [A_172] : k2_zfmisc_1(A_172,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_542,c_637])).

tff(c_487,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_496,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_488,c_487])).

tff(c_497,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_44,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_503,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_497,c_488,c_44])).

tff(c_679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_503])).

tff(c_680,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_687,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_680,c_488,c_44])).

tff(c_801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_794,c_687])).

tff(c_803,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_802,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_812,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_803,c_802])).

tff(c_813,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_812])).

tff(c_804,plain,(
    ! [A_4] : r1_xboole_0(A_4,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_10])).

tff(c_814,plain,(
    ! [A_4] : r1_xboole_0(A_4,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_804])).

tff(c_830,plain,(
    ! [A_207,B_208] :
      ( ~ r2_hidden(A_207,B_208)
      | ~ r1_xboole_0(k1_tarski(A_207),B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_835,plain,(
    ! [A_207] : ~ r2_hidden(A_207,'#skF_10') ),
    inference(resolution,[status(thm)],[c_814,c_830])).

tff(c_855,plain,(
    ! [B_223] :
      ( r2_hidden('#skF_1'('#skF_10',B_223),B_223)
      | B_223 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_847,c_835])).

tff(c_951,plain,(
    ! [A_237,B_238,D_239] :
      ( r2_hidden('#skF_8'(A_237,B_238,k2_zfmisc_1(A_237,B_238),D_239),B_238)
      | ~ r2_hidden(D_239,k2_zfmisc_1(A_237,B_238)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_961,plain,(
    ! [D_240,A_241] : ~ r2_hidden(D_240,k2_zfmisc_1(A_241,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_951,c_835])).

tff(c_996,plain,(
    ! [A_241] : k2_zfmisc_1(A_241,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_855,c_961])).

tff(c_816,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_803])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_828,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_813,c_816,c_48])).

tff(c_1003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_828])).

tff(c_1004,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_812])).

tff(c_1006,plain,(
    ! [A_4] : r1_xboole_0(A_4,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_804])).

tff(c_1023,plain,(
    ! [A_243,B_244] :
      ( ~ r2_hidden(A_243,B_244)
      | ~ r1_xboole_0(k1_tarski(A_243),B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1028,plain,(
    ! [A_243] : ~ r2_hidden(A_243,'#skF_9') ),
    inference(resolution,[status(thm)],[c_1006,c_1023])).

tff(c_1050,plain,(
    ! [B_259] :
      ( r2_hidden('#skF_1'('#skF_9',B_259),B_259)
      | B_259 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1042,c_1028])).

tff(c_1084,plain,(
    ! [A_267,B_268,D_269] :
      ( r2_hidden('#skF_7'(A_267,B_268,k2_zfmisc_1(A_267,B_268),D_269),A_267)
      | ~ r2_hidden(D_269,k2_zfmisc_1(A_267,B_268)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1096,plain,(
    ! [D_273,B_274] : ~ r2_hidden(D_273,k2_zfmisc_1('#skF_9',B_274)) ),
    inference(resolution,[status(thm)],[c_1084,c_1028])).

tff(c_1128,plain,(
    ! [B_274] : k2_zfmisc_1('#skF_9',B_274) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1050,c_1096])).

tff(c_1008,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_803])).

tff(c_1022,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1004,c_1008,c_48])).

tff(c_1135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1128,c_1022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.39  
% 2.59/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.39  %$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 2.59/1.39  
% 2.59/1.39  %Foreground sorts:
% 2.59/1.39  
% 2.59/1.39  
% 2.59/1.39  %Background operators:
% 2.59/1.39  
% 2.59/1.39  
% 2.59/1.39  %Foreground operators:
% 2.59/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.39  tff('#skF_11', type, '#skF_11': $i).
% 2.59/1.39  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.59/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.59/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.59/1.39  tff('#skF_10', type, '#skF_10': $i).
% 2.59/1.39  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.59/1.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.59/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.39  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.59/1.39  tff('#skF_9', type, '#skF_9': $i).
% 2.59/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.59/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.59/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.39  tff('#skF_12', type, '#skF_12': $i).
% 2.59/1.39  
% 2.59/1.41  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.59/1.41  tff(f_64, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.59/1.41  tff(f_34, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.59/1.41  tff(f_51, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.59/1.41  tff(f_57, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.59/1.41  tff(f_46, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.59/1.41  tff(c_1042, plain, (![A_258, B_259]: (r2_hidden('#skF_1'(A_258, B_259), B_259) | r2_hidden('#skF_2'(A_258, B_259), A_258) | B_259=A_258)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.41  tff(c_847, plain, (![A_222, B_223]: (r2_hidden('#skF_1'(A_222, B_223), B_223) | r2_hidden('#skF_2'(A_222, B_223), A_222) | B_223=A_222)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.41  tff(c_715, plain, (![A_190, B_191]: (r2_hidden('#skF_1'(A_190, B_191), B_191) | r2_hidden('#skF_2'(A_190, B_191), A_190) | B_191=A_190)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.41  tff(c_393, plain, (![A_120, B_121]: (r2_hidden('#skF_1'(A_120, B_121), B_121) | r2_hidden('#skF_2'(A_120, B_121), A_120) | B_121=A_120)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.41  tff(c_46, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.41  tff(c_57, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_46])).
% 2.59/1.41  tff(c_93, plain, (![A_63, B_64]: (r2_hidden('#skF_1'(A_63, B_64), B_64) | r2_hidden('#skF_2'(A_63, B_64), A_63) | B_64=A_63)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.41  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.59/1.41  tff(c_58, plain, (![A_46, B_47]: (~r2_hidden(A_46, B_47) | ~r1_xboole_0(k1_tarski(A_46), B_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.41  tff(c_63, plain, (![A_46]: (~r2_hidden(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_58])).
% 2.59/1.41  tff(c_107, plain, (![B_64]: (r2_hidden('#skF_1'(k1_xboole_0, B_64), B_64) | k1_xboole_0=B_64)), inference(resolution, [status(thm)], [c_93, c_63])).
% 2.59/1.41  tff(c_50, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.41  tff(c_56, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_50])).
% 2.59/1.41  tff(c_54, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.41  tff(c_65, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 2.59/1.41  tff(c_119, plain, (![A_66, B_67, C_68, D_69]: (r2_hidden(k4_tarski(A_66, B_67), k2_zfmisc_1(C_68, D_69)) | ~r2_hidden(B_67, D_69) | ~r2_hidden(A_66, C_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.59/1.41  tff(c_128, plain, (![A_66, B_67]: (r2_hidden(k4_tarski(A_66, B_67), k1_xboole_0) | ~r2_hidden(B_67, '#skF_12') | ~r2_hidden(A_66, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_119])).
% 2.59/1.41  tff(c_131, plain, (![B_67, A_66]: (~r2_hidden(B_67, '#skF_12') | ~r2_hidden(A_66, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_63, c_128])).
% 2.59/1.41  tff(c_133, plain, (![A_70]: (~r2_hidden(A_70, '#skF_11'))), inference(splitLeft, [status(thm)], [c_131])).
% 2.59/1.41  tff(c_137, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_107, c_133])).
% 2.59/1.41  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_137])).
% 2.59/1.41  tff(c_153, plain, (![B_71]: (~r2_hidden(B_71, '#skF_12'))), inference(splitRight, [status(thm)], [c_131])).
% 2.59/1.41  tff(c_157, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_107, c_153])).
% 2.59/1.41  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_157])).
% 2.59/1.41  tff(c_172, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_54])).
% 2.59/1.41  tff(c_174, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_172])).
% 2.59/1.41  tff(c_173, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.59/1.41  tff(c_361, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_173])).
% 2.59/1.41  tff(c_197, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), B_87) | r2_hidden('#skF_2'(A_86, B_87), A_86) | B_87=A_86)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.41  tff(c_175, plain, (![A_46]: (~r2_hidden(A_46, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_63])).
% 2.59/1.41  tff(c_211, plain, (![B_87]: (r2_hidden('#skF_1'('#skF_10', B_87), B_87) | B_87='#skF_10')), inference(resolution, [status(thm)], [c_197, c_175])).
% 2.59/1.41  tff(c_306, plain, (![A_101, B_102, D_103]: (r2_hidden('#skF_8'(A_101, B_102, k2_zfmisc_1(A_101, B_102), D_103), B_102) | ~r2_hidden(D_103, k2_zfmisc_1(A_101, B_102)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.59/1.41  tff(c_316, plain, (![D_104, A_105]: (~r2_hidden(D_104, k2_zfmisc_1(A_105, '#skF_10')))), inference(resolution, [status(thm)], [c_306, c_175])).
% 2.59/1.41  tff(c_352, plain, (![A_105]: (k2_zfmisc_1(A_105, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_211, c_316])).
% 2.59/1.41  tff(c_52, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.41  tff(c_190, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10' | k2_zfmisc_1('#skF_11', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_174, c_52])).
% 2.59/1.41  tff(c_191, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(splitLeft, [status(thm)], [c_190])).
% 2.59/1.41  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_352, c_191])).
% 2.59/1.41  tff(c_359, plain, (k2_zfmisc_1('#skF_11', '#skF_12')='#skF_10'), inference(splitRight, [status(thm)], [c_190])).
% 2.59/1.41  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_361, c_359])).
% 2.59/1.41  tff(c_363, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_172])).
% 2.59/1.41  tff(c_365, plain, (![A_46]: (~r2_hidden(A_46, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_63])).
% 2.59/1.41  tff(c_401, plain, (![B_121]: (r2_hidden('#skF_1'('#skF_9', B_121), B_121) | B_121='#skF_9')), inference(resolution, [status(thm)], [c_393, c_365])).
% 2.59/1.41  tff(c_435, plain, (![A_129, B_130, D_131]: (r2_hidden('#skF_7'(A_129, B_130, k2_zfmisc_1(A_129, B_130), D_131), A_129) | ~r2_hidden(D_131, k2_zfmisc_1(A_129, B_130)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.59/1.41  tff(c_447, plain, (![D_135, B_136]: (~r2_hidden(D_135, k2_zfmisc_1('#skF_9', B_136)))), inference(resolution, [status(thm)], [c_435, c_365])).
% 2.59/1.41  tff(c_479, plain, (![B_136]: (k2_zfmisc_1('#skF_9', B_136)='#skF_9')), inference(resolution, [status(thm)], [c_401, c_447])).
% 2.59/1.41  tff(c_381, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_363, c_173])).
% 2.59/1.41  tff(c_382, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_363, c_363, c_52])).
% 2.59/1.41  tff(c_383, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_381, c_382])).
% 2.59/1.41  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_479, c_383])).
% 2.59/1.41  tff(c_488, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_46])).
% 2.59/1.41  tff(c_490, plain, (![A_4]: (r1_xboole_0(A_4, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_488, c_10])).
% 2.59/1.41  tff(c_689, plain, (![A_173, B_174]: (~r2_hidden(A_173, B_174) | ~r1_xboole_0(k1_tarski(A_173), B_174))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.41  tff(c_694, plain, (![A_173]: (~r2_hidden(A_173, '#skF_12'))), inference(resolution, [status(thm)], [c_490, c_689])).
% 2.59/1.41  tff(c_729, plain, (![B_191]: (r2_hidden('#skF_1'('#skF_12', B_191), B_191) | B_191='#skF_12')), inference(resolution, [status(thm)], [c_715, c_694])).
% 2.59/1.41  tff(c_750, plain, (![A_197, B_198, D_199]: (r2_hidden('#skF_7'(A_197, B_198, k2_zfmisc_1(A_197, B_198), D_199), A_197) | ~r2_hidden(D_199, k2_zfmisc_1(A_197, B_198)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.59/1.41  tff(c_762, plain, (![D_203, B_204]: (~r2_hidden(D_203, k2_zfmisc_1('#skF_12', B_204)))), inference(resolution, [status(thm)], [c_750, c_694])).
% 2.59/1.41  tff(c_794, plain, (![B_204]: (k2_zfmisc_1('#skF_12', B_204)='#skF_12')), inference(resolution, [status(thm)], [c_729, c_762])).
% 2.59/1.41  tff(c_529, plain, (![A_153, B_154]: (r2_hidden('#skF_1'(A_153, B_154), B_154) | r2_hidden('#skF_2'(A_153, B_154), A_153) | B_154=A_153)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.41  tff(c_506, plain, (![A_138, B_139]: (~r2_hidden(A_138, B_139) | ~r1_xboole_0(k1_tarski(A_138), B_139))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.41  tff(c_511, plain, (![A_138]: (~r2_hidden(A_138, '#skF_12'))), inference(resolution, [status(thm)], [c_490, c_506])).
% 2.59/1.41  tff(c_542, plain, (![B_154]: (r2_hidden('#skF_1'('#skF_12', B_154), B_154) | B_154='#skF_12')), inference(resolution, [status(thm)], [c_529, c_511])).
% 2.59/1.41  tff(c_627, plain, (![A_168, B_169, D_170]: (r2_hidden('#skF_8'(A_168, B_169, k2_zfmisc_1(A_168, B_169), D_170), B_169) | ~r2_hidden(D_170, k2_zfmisc_1(A_168, B_169)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.59/1.41  tff(c_637, plain, (![D_171, A_172]: (~r2_hidden(D_171, k2_zfmisc_1(A_172, '#skF_12')))), inference(resolution, [status(thm)], [c_627, c_511])).
% 2.59/1.41  tff(c_672, plain, (![A_172]: (k2_zfmisc_1(A_172, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_542, c_637])).
% 2.59/1.41  tff(c_487, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_46])).
% 2.59/1.41  tff(c_496, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_488, c_488, c_487])).
% 2.59/1.41  tff(c_497, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_496])).
% 2.59/1.41  tff(c_44, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.41  tff(c_503, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_488, c_497, c_488, c_44])).
% 2.59/1.41  tff(c_679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_672, c_503])).
% 2.59/1.41  tff(c_680, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_496])).
% 2.59/1.41  tff(c_687, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_488, c_680, c_488, c_44])).
% 2.59/1.41  tff(c_801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_794, c_687])).
% 2.59/1.41  tff(c_803, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_50])).
% 2.59/1.41  tff(c_802, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_50])).
% 2.59/1.41  tff(c_812, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_803, c_803, c_802])).
% 2.59/1.41  tff(c_813, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_812])).
% 2.59/1.41  tff(c_804, plain, (![A_4]: (r1_xboole_0(A_4, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_803, c_10])).
% 2.59/1.41  tff(c_814, plain, (![A_4]: (r1_xboole_0(A_4, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_813, c_804])).
% 2.59/1.41  tff(c_830, plain, (![A_207, B_208]: (~r2_hidden(A_207, B_208) | ~r1_xboole_0(k1_tarski(A_207), B_208))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.41  tff(c_835, plain, (![A_207]: (~r2_hidden(A_207, '#skF_10'))), inference(resolution, [status(thm)], [c_814, c_830])).
% 2.59/1.41  tff(c_855, plain, (![B_223]: (r2_hidden('#skF_1'('#skF_10', B_223), B_223) | B_223='#skF_10')), inference(resolution, [status(thm)], [c_847, c_835])).
% 2.59/1.41  tff(c_951, plain, (![A_237, B_238, D_239]: (r2_hidden('#skF_8'(A_237, B_238, k2_zfmisc_1(A_237, B_238), D_239), B_238) | ~r2_hidden(D_239, k2_zfmisc_1(A_237, B_238)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.59/1.41  tff(c_961, plain, (![D_240, A_241]: (~r2_hidden(D_240, k2_zfmisc_1(A_241, '#skF_10')))), inference(resolution, [status(thm)], [c_951, c_835])).
% 2.59/1.41  tff(c_996, plain, (![A_241]: (k2_zfmisc_1(A_241, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_855, c_961])).
% 2.59/1.41  tff(c_816, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_813, c_803])).
% 2.59/1.41  tff(c_48, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.41  tff(c_828, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_816, c_813, c_816, c_48])).
% 2.59/1.41  tff(c_1003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_996, c_828])).
% 2.59/1.41  tff(c_1004, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_812])).
% 2.59/1.41  tff(c_1006, plain, (![A_4]: (r1_xboole_0(A_4, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_804])).
% 2.59/1.41  tff(c_1023, plain, (![A_243, B_244]: (~r2_hidden(A_243, B_244) | ~r1_xboole_0(k1_tarski(A_243), B_244))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.41  tff(c_1028, plain, (![A_243]: (~r2_hidden(A_243, '#skF_9'))), inference(resolution, [status(thm)], [c_1006, c_1023])).
% 2.59/1.41  tff(c_1050, plain, (![B_259]: (r2_hidden('#skF_1'('#skF_9', B_259), B_259) | B_259='#skF_9')), inference(resolution, [status(thm)], [c_1042, c_1028])).
% 2.59/1.41  tff(c_1084, plain, (![A_267, B_268, D_269]: (r2_hidden('#skF_7'(A_267, B_268, k2_zfmisc_1(A_267, B_268), D_269), A_267) | ~r2_hidden(D_269, k2_zfmisc_1(A_267, B_268)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.59/1.41  tff(c_1096, plain, (![D_273, B_274]: (~r2_hidden(D_273, k2_zfmisc_1('#skF_9', B_274)))), inference(resolution, [status(thm)], [c_1084, c_1028])).
% 2.59/1.41  tff(c_1128, plain, (![B_274]: (k2_zfmisc_1('#skF_9', B_274)='#skF_9')), inference(resolution, [status(thm)], [c_1050, c_1096])).
% 2.59/1.41  tff(c_1008, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_803])).
% 2.59/1.41  tff(c_1022, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1004, c_1008, c_48])).
% 2.59/1.41  tff(c_1135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1128, c_1022])).
% 2.59/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.41  
% 2.59/1.41  Inference rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Ref     : 0
% 2.59/1.41  #Sup     : 190
% 2.59/1.41  #Fact    : 0
% 2.59/1.41  #Define  : 0
% 2.59/1.41  #Split   : 10
% 2.59/1.41  #Chain   : 0
% 2.59/1.41  #Close   : 0
% 2.59/1.41  
% 2.59/1.41  Ordering : KBO
% 2.59/1.41  
% 2.59/1.41  Simplification rules
% 2.59/1.41  ----------------------
% 2.59/1.41  #Subsume      : 78
% 2.59/1.41  #Demod        : 110
% 2.59/1.41  #Tautology    : 68
% 2.59/1.41  #SimpNegUnit  : 16
% 2.59/1.41  #BackRed      : 32
% 2.59/1.41  
% 2.59/1.41  #Partial instantiations: 0
% 2.59/1.41  #Strategies tried      : 1
% 2.59/1.41  
% 2.59/1.41  Timing (in seconds)
% 2.59/1.41  ----------------------
% 2.59/1.42  Preprocessing        : 0.30
% 2.59/1.42  Parsing              : 0.15
% 2.59/1.42  CNF conversion       : 0.03
% 2.59/1.42  Main loop            : 0.33
% 2.59/1.42  Inferencing          : 0.14
% 2.59/1.42  Reduction            : 0.08
% 2.59/1.42  Demodulation         : 0.05
% 2.59/1.42  BG Simplification    : 0.02
% 2.59/1.42  Subsumption          : 0.06
% 2.59/1.42  Abstraction          : 0.02
% 2.59/1.42  MUC search           : 0.00
% 2.59/1.42  Cooper               : 0.00
% 2.59/1.42  Total                : 0.68
% 2.59/1.42  Index Insertion      : 0.00
% 2.59/1.42  Index Deletion       : 0.00
% 2.59/1.42  Index Matching       : 0.00
% 2.59/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
