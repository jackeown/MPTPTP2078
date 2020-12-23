%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0301+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:04 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 868 expanded)
%              Number of leaves         :   26 ( 269 expanded)
%              Depth                    :   13
%              Number of atoms          :  227 (1641 expanded)
%              Number of equality atoms :   97 ( 995 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_32,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_7'(A_38),A_38)
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_45,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_26])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_61,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_69,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_74,plain,(
    ! [E_44,F_45,A_46,B_47] :
      ( r2_hidden(k4_tarski(E_44,F_45),k2_zfmisc_1(A_46,B_47))
      | ~ r2_hidden(F_45,B_47)
      | ~ r2_hidden(E_44,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [B_37,A_36] :
      ( ~ v1_xboole_0(B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_82,plain,(
    ! [A_48,B_49,F_50,E_51] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_48,B_49))
      | ~ r2_hidden(F_50,B_49)
      | ~ r2_hidden(E_51,A_48) ) ),
    inference(resolution,[status(thm)],[c_74,c_30])).

tff(c_84,plain,(
    ! [F_50,E_51] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(F_50,'#skF_11')
      | ~ r2_hidden(E_51,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_82])).

tff(c_86,plain,(
    ! [F_50,E_51] :
      ( ~ r2_hidden(F_50,'#skF_11')
      | ~ r2_hidden(E_51,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_84])).

tff(c_95,plain,(
    ! [E_54] : ~ r2_hidden(E_54,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_99,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_32,c_95])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_99])).

tff(c_105,plain,(
    ! [F_55] : ~ r2_hidden(F_55,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_109,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_32,c_105])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_109])).

tff(c_114,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_116,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_121,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_50])).

tff(c_118,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_7'(A_38),A_38)
      | A_38 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_32])).

tff(c_150,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_hidden('#skF_6'(A_66,B_67,k2_zfmisc_1(A_66,B_67),D_68),B_67)
      | ~ r2_hidden(D_68,k2_zfmisc_1(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_160,plain,(
    ! [B_72,D_73,A_74] :
      ( ~ v1_xboole_0(B_72)
      | ~ r2_hidden(D_73,k2_zfmisc_1(A_74,B_72)) ) ),
    inference(resolution,[status(thm)],[c_150,c_30])).

tff(c_180,plain,(
    ! [B_75,A_76] :
      ( ~ v1_xboole_0(B_75)
      | k2_zfmisc_1(A_76,B_75) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_118,c_160])).

tff(c_183,plain,(
    ! [A_76] : k2_zfmisc_1(A_76,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_121,c_180])).

tff(c_42,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_68,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_117,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_68])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_117])).

tff(c_187,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_192,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_7'(A_38),A_38)
      | A_38 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_32])).

tff(c_8,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_1)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_195,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_50])).

tff(c_223,plain,(
    ! [A_87,B_88,D_89] :
      ( r2_hidden('#skF_6'(A_87,B_88,k2_zfmisc_1(A_87,B_88),D_89),B_88)
      | ~ r2_hidden(D_89,k2_zfmisc_1(A_87,B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_228,plain,(
    ! [B_90,D_91,A_92] :
      ( ~ v1_xboole_0(B_90)
      | ~ r2_hidden(D_91,k2_zfmisc_1(A_92,B_90)) ) ),
    inference(resolution,[status(thm)],[c_223,c_30])).

tff(c_253,plain,(
    ! [B_96,A_97] :
      ( ~ v1_xboole_0(B_96)
      | k2_zfmisc_1(A_97,B_96) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_192,c_228])).

tff(c_257,plain,(
    ! [A_98] : k2_zfmisc_1(A_98,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_195,c_253])).

tff(c_227,plain,(
    ! [B_88,D_89,A_87] :
      ( ~ v1_xboole_0(B_88)
      | ~ r2_hidden(D_89,k2_zfmisc_1(A_87,B_88)) ) ),
    inference(resolution,[status(thm)],[c_223,c_30])).

tff(c_265,plain,(
    ! [D_89] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(D_89,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_227])).

tff(c_284,plain,(
    ! [D_99] : ~ r2_hidden(D_99,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_265])).

tff(c_303,plain,(
    ! [D_103,B_104] : ~ r2_hidden(D_103,k2_zfmisc_1('#skF_8',B_104)) ),
    inference(resolution,[status(thm)],[c_8,c_284])).

tff(c_326,plain,(
    ! [B_104] : k2_zfmisc_1('#skF_8',B_104) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_192,c_303])).

tff(c_191,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_68])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_191])).

tff(c_332,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_342,plain,(
    ! [E_105,F_106,A_107,B_108] :
      ( r2_hidden(k4_tarski(E_105,F_106),k2_zfmisc_1(A_107,B_108))
      | ~ r2_hidden(F_106,B_108)
      | ~ r2_hidden(E_105,A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_353,plain,(
    ! [A_109,B_110,F_111,E_112] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_109,B_110))
      | ~ r2_hidden(F_111,B_110)
      | ~ r2_hidden(E_112,A_109) ) ),
    inference(resolution,[status(thm)],[c_342,c_30])).

tff(c_355,plain,(
    ! [F_111,E_112] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(F_111,'#skF_9')
      | ~ r2_hidden(E_112,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_353])).

tff(c_359,plain,(
    ! [F_111,E_112] :
      ( ~ r2_hidden(F_111,'#skF_9')
      | ~ r2_hidden(E_112,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_355])).

tff(c_363,plain,(
    ! [E_113] : ~ r2_hidden(E_113,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_359])).

tff(c_368,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_32,c_363])).

tff(c_381,plain,(
    '#skF_11' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_61])).

tff(c_599,plain,(
    ! [A_136] :
      ( r2_hidden('#skF_7'(A_136),A_136)
      | A_136 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_32])).

tff(c_380,plain,(
    '#skF_10' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_62])).

tff(c_544,plain,(
    ! [A_132] :
      ( r2_hidden('#skF_7'(A_132),A_132)
      | A_132 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_32])).

tff(c_331,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_357,plain,(
    ! [F_111,E_112] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(F_111,'#skF_11')
      | ~ r2_hidden(E_112,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_353])).

tff(c_361,plain,(
    ! [F_111,E_112] :
      ( ~ r2_hidden(F_111,'#skF_11')
      | ~ r2_hidden(E_112,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_357])).

tff(c_455,plain,(
    ! [E_112] : ~ r2_hidden(E_112,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_560,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_544,c_455])).

tff(c_578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_380,c_560])).

tff(c_579,plain,(
    ! [F_111] : ~ r2_hidden(F_111,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_607,plain,(
    '#skF_11' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_599,c_579])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_607])).

tff(c_625,plain,(
    ! [F_137] : ~ r2_hidden(F_137,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_630,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_32,c_625])).

tff(c_635,plain,(
    '#skF_11' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_61])).

tff(c_851,plain,(
    ! [A_158] :
      ( r2_hidden('#skF_7'(A_158),A_158)
      | A_158 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_32])).

tff(c_634,plain,(
    '#skF_10' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_62])).

tff(c_796,plain,(
    ! [A_154] :
      ( r2_hidden('#skF_7'(A_154),A_154)
      | A_154 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_32])).

tff(c_709,plain,(
    ! [E_112] : ~ r2_hidden(E_112,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_812,plain,(
    '#skF_10' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_796,c_709])).

tff(c_830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_634,c_812])).

tff(c_831,plain,(
    ! [F_111] : ~ r2_hidden(F_111,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_859,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_851,c_831])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_635,c_859])).

tff(c_877,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_891,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_877,c_877,c_40])).

tff(c_892,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_891])).

tff(c_896,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_877])).

tff(c_917,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_7'(A_38),A_38)
      | A_38 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_32])).

tff(c_879,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_50])).

tff(c_894,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_879])).

tff(c_932,plain,(
    ! [A_169,B_170,D_171] :
      ( r2_hidden('#skF_6'(A_169,B_170,k2_zfmisc_1(A_169,B_170),D_171),B_170)
      | ~ r2_hidden(D_171,k2_zfmisc_1(A_169,B_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_937,plain,(
    ! [B_172,D_173,A_174] :
      ( ~ v1_xboole_0(B_172)
      | ~ r2_hidden(D_173,k2_zfmisc_1(A_174,B_172)) ) ),
    inference(resolution,[status(thm)],[c_932,c_30])).

tff(c_962,plain,(
    ! [B_178,A_179] :
      ( ~ v1_xboole_0(B_178)
      | k2_zfmisc_1(A_179,B_178) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_917,c_937])).

tff(c_966,plain,(
    ! [A_180] : k2_zfmisc_1(A_180,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_894,c_962])).

tff(c_936,plain,(
    ! [B_170,D_171,A_169] :
      ( ~ v1_xboole_0(B_170)
      | ~ r2_hidden(D_171,k2_zfmisc_1(A_169,B_170)) ) ),
    inference(resolution,[status(thm)],[c_932,c_30])).

tff(c_974,plain,(
    ! [D_171] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(D_171,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_936])).

tff(c_993,plain,(
    ! [D_181] : ~ r2_hidden(D_181,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_974])).

tff(c_1037,plain,(
    ! [D_185,B_186] : ~ r2_hidden(D_185,k2_zfmisc_1('#skF_8',B_186)) ),
    inference(resolution,[status(thm)],[c_8,c_993])).

tff(c_1070,plain,(
    ! [B_186] : k2_zfmisc_1('#skF_8',B_186) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_917,c_1037])).

tff(c_876,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_916,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_876])).

tff(c_1074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1070,c_916])).

tff(c_1075,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_891])).

tff(c_1078,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_879])).

tff(c_1080,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_877])).

tff(c_1103,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_7'(A_38),A_38)
      | A_38 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_32])).

tff(c_1117,plain,(
    ! [A_193,B_194,D_195] :
      ( r2_hidden('#skF_6'(A_193,B_194,k2_zfmisc_1(A_193,B_194),D_195),B_194)
      | ~ r2_hidden(D_195,k2_zfmisc_1(A_193,B_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1122,plain,(
    ! [B_196,D_197,A_198] :
      ( ~ v1_xboole_0(B_196)
      | ~ r2_hidden(D_197,k2_zfmisc_1(A_198,B_196)) ) ),
    inference(resolution,[status(thm)],[c_1117,c_30])).

tff(c_1137,plain,(
    ! [B_199,A_200] :
      ( ~ v1_xboole_0(B_199)
      | k2_zfmisc_1(A_200,B_199) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1103,c_1122])).

tff(c_1140,plain,(
    ! [A_200] : k2_zfmisc_1(A_200,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1078,c_1137])).

tff(c_1094,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_876])).

tff(c_1143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_1094])).

tff(c_1145,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1144,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1176,plain,
    ( '#skF_11' = '#skF_8'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_1145,c_1144])).

tff(c_1177,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1176])).

tff(c_1158,plain,(
    v1_xboole_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_50])).

tff(c_1180,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_1158])).

tff(c_1181,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_1145])).

tff(c_1204,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_7'(A_38),A_38)
      | A_38 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_32])).

tff(c_1218,plain,(
    ! [A_212,B_213,D_214] :
      ( r2_hidden('#skF_6'(A_212,B_213,k2_zfmisc_1(A_212,B_213),D_214),B_213)
      | ~ r2_hidden(D_214,k2_zfmisc_1(A_212,B_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1223,plain,(
    ! [B_215,D_216,A_217] :
      ( ~ v1_xboole_0(B_215)
      | ~ r2_hidden(D_216,k2_zfmisc_1(A_217,B_215)) ) ),
    inference(resolution,[status(thm)],[c_1218,c_30])).

tff(c_1238,plain,(
    ! [B_218,A_219] :
      ( ~ v1_xboole_0(B_218)
      | k2_zfmisc_1(A_219,B_218) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1204,c_1223])).

tff(c_1241,plain,(
    ! [A_219] : k2_zfmisc_1(A_219,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1180,c_1238])).

tff(c_34,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1146,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_1155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_1146])).

tff(c_1156,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1196,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_1156])).

tff(c_1254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_1196])).

tff(c_1255,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1176])).

tff(c_1260,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_1145])).

tff(c_1283,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_7'(A_38),A_38)
      | A_38 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_32])).

tff(c_1259,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1255,c_1158])).

tff(c_1299,plain,(
    ! [A_233,B_234,D_235] :
      ( r2_hidden('#skF_6'(A_233,B_234,k2_zfmisc_1(A_233,B_234),D_235),B_234)
      | ~ r2_hidden(D_235,k2_zfmisc_1(A_233,B_234)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1304,plain,(
    ! [B_236,D_237,A_238] :
      ( ~ v1_xboole_0(B_236)
      | ~ r2_hidden(D_237,k2_zfmisc_1(A_238,B_236)) ) ),
    inference(resolution,[status(thm)],[c_1299,c_30])).

tff(c_1319,plain,(
    ! [B_239,A_240] :
      ( ~ v1_xboole_0(B_239)
      | k2_zfmisc_1(A_240,B_239) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1283,c_1304])).

tff(c_1333,plain,(
    ! [A_244] : k2_zfmisc_1(A_244,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1259,c_1319])).

tff(c_1303,plain,(
    ! [B_234,D_235,A_233] :
      ( ~ v1_xboole_0(B_234)
      | ~ r2_hidden(D_235,k2_zfmisc_1(A_233,B_234)) ) ),
    inference(resolution,[status(thm)],[c_1299,c_30])).

tff(c_1341,plain,(
    ! [D_235] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(D_235,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1333,c_1303])).

tff(c_1360,plain,(
    ! [D_245] : ~ r2_hidden(D_245,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1259,c_1341])).

tff(c_1378,plain,(
    ! [D_246,B_247] : ~ r2_hidden(D_246,k2_zfmisc_1('#skF_8',B_247)) ),
    inference(resolution,[status(thm)],[c_8,c_1360])).

tff(c_1401,plain,(
    ! [B_247] : k2_zfmisc_1('#skF_8',B_247) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1283,c_1378])).

tff(c_1282,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_1156])).

tff(c_1441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1282])).

%------------------------------------------------------------------------------
