%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:46 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 737 expanded)
%              Number of leaves         :   26 ( 229 expanded)
%              Depth                    :    9
%              Number of atoms          :  221 (1472 expanded)
%              Number of equality atoms :  109 (1080 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

tff(c_1980,plain,(
    ! [A_273,B_274] :
      ( r2_hidden('#skF_1'(A_273,B_274),B_274)
      | r2_hidden('#skF_2'(A_273,B_274),A_273)
      | B_274 = A_273 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1746,plain,(
    ! [A_242,B_243] :
      ( r2_hidden('#skF_1'(A_242,B_243),B_243)
      | r2_hidden('#skF_2'(A_242,B_243),A_242)
      | B_243 = A_242 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1587,plain,(
    ! [A_211,B_212] :
      ( r2_hidden('#skF_1'(A_211,B_212),B_212)
      | r2_hidden('#skF_2'(A_211,B_212),A_211)
      | B_212 = A_211 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_552,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(A_122,B_123),B_123)
      | r2_hidden('#skF_2'(A_122,B_123),A_122)
      | B_123 = A_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_527,plain,(
    ! [B_113,A_114] :
      ( ~ r2_hidden(B_113,A_114)
      | k4_xboole_0(A_114,k1_tarski(B_113)) != A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_536,plain,(
    ! [B_113] : ~ r2_hidden(B_113,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_527])).

tff(c_566,plain,(
    ! [B_123] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_123),B_123)
      | k1_xboole_0 = B_123 ) ),
    inference(resolution,[status(thm)],[c_552,c_536])).

tff(c_434,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_1'(A_95,B_96),B_96)
      | r2_hidden('#skF_2'(A_95,B_96),A_95)
      | B_96 = A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_223,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),B_67)
      | r2_hidden('#skF_2'(A_66,B_67),A_66)
      | B_67 = A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_96,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(A_47,B_48),B_48)
      | r2_hidden('#skF_2'(A_47,B_48),A_47)
      | B_48 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [B_44,A_45] :
      ( ~ r2_hidden(B_44,A_45)
      | k4_xboole_0(A_45,k1_tarski(B_44)) != A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_94,plain,(
    ! [B_44] : ~ r2_hidden(B_44,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_85])).

tff(c_103,plain,(
    ! [B_48] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_48),B_48)
      | k1_xboole_0 = B_48 ) ),
    inference(resolution,[status(thm)],[c_96,c_94])).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_80,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_136,plain,(
    ! [E_56,F_57,A_58,B_59] :
      ( r2_hidden(k4_tarski(E_56,F_57),k2_zfmisc_1(A_58,B_59))
      | ~ r2_hidden(F_57,B_59)
      | ~ r2_hidden(E_56,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_139,plain,(
    ! [E_56,F_57] :
      ( r2_hidden(k4_tarski(E_56,F_57),k1_xboole_0)
      | ~ r2_hidden(F_57,'#skF_12')
      | ~ r2_hidden(E_56,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_136])).

tff(c_140,plain,(
    ! [F_57,E_56] :
      ( ~ r2_hidden(F_57,'#skF_12')
      | ~ r2_hidden(E_56,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_139])).

tff(c_142,plain,(
    ! [E_60] : ~ r2_hidden(E_60,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_150,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_103,c_142])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_150])).

tff(c_163,plain,(
    ! [F_61] : ~ r2_hidden(F_61,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_171,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_103,c_163])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_171])).

tff(c_183,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_185,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_189,plain,(
    ! [A_4] : k4_xboole_0('#skF_10',A_4) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_185,c_10])).

tff(c_212,plain,(
    ! [B_63,A_64] :
      ( ~ r2_hidden(B_63,A_64)
      | k4_xboole_0(A_64,k1_tarski(B_63)) != A_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_220,plain,(
    ! [B_63] : ~ r2_hidden(B_63,'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_212])).

tff(c_230,plain,(
    ! [B_67] :
      ( r2_hidden('#skF_1'('#skF_10',B_67),B_67)
      | B_67 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_223,c_220])).

tff(c_336,plain,(
    ! [A_86,B_87,D_88] :
      ( r2_hidden('#skF_8'(A_86,B_87,k2_zfmisc_1(A_86,B_87),D_88),B_87)
      | ~ r2_hidden(D_88,k2_zfmisc_1(A_86,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_346,plain,(
    ! [D_89,A_90] : ~ r2_hidden(D_89,k2_zfmisc_1(A_90,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_336,c_220])).

tff(c_387,plain,(
    ! [A_90] : k2_zfmisc_1(A_90,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_230,c_346])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_79,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_186,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_79])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_186])).

tff(c_394,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_401,plain,(
    ! [A_4] : k4_xboole_0('#skF_9',A_4) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_394,c_10])).

tff(c_423,plain,(
    ! [B_92,A_93] :
      ( ~ r2_hidden(B_92,A_93)
      | k4_xboole_0(A_93,k1_tarski(B_92)) != A_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_431,plain,(
    ! [B_92] : ~ r2_hidden(B_92,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_423])).

tff(c_441,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_1'('#skF_9',B_96),B_96)
      | B_96 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_434,c_431])).

tff(c_475,plain,(
    ! [A_108,B_109,D_110] :
      ( r2_hidden('#skF_7'(A_108,B_109,k2_zfmisc_1(A_108,B_109),D_110),A_108)
      | ~ r2_hidden(D_110,k2_zfmisc_1(A_108,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_481,plain,(
    ! [D_111,B_112] : ~ r2_hidden(D_111,k2_zfmisc_1('#skF_9',B_112)) ),
    inference(resolution,[status(thm)],[c_475,c_431])).

tff(c_509,plain,(
    ! [B_112] : k2_zfmisc_1('#skF_9',B_112) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_441,c_481])).

tff(c_398,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_79])).

tff(c_515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_398])).

tff(c_517,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_578,plain,(
    ! [E_125,F_126,A_127,B_128] :
      ( r2_hidden(k4_tarski(E_125,F_126),k2_zfmisc_1(A_127,B_128))
      | ~ r2_hidden(F_126,B_128)
      | ~ r2_hidden(E_125,A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_581,plain,(
    ! [E_125,F_126] :
      ( r2_hidden(k4_tarski(E_125,F_126),k1_xboole_0)
      | ~ r2_hidden(F_126,'#skF_10')
      | ~ r2_hidden(E_125,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_578])).

tff(c_585,plain,(
    ! [F_126,E_125] :
      ( ~ r2_hidden(F_126,'#skF_10')
      | ~ r2_hidden(E_125,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_536,c_581])).

tff(c_588,plain,(
    ! [E_129] : ~ r2_hidden(E_129,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_603,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_566,c_588])).

tff(c_610,plain,(
    '#skF_9' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_59])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_908,plain,(
    ! [B_150] :
      ( r2_hidden('#skF_1'('#skF_9',B_150),B_150)
      | B_150 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_8,c_588])).

tff(c_611,plain,(
    '#skF_11' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_58])).

tff(c_742,plain,(
    ! [B_139] :
      ( r2_hidden('#skF_1'('#skF_9',B_139),B_139)
      | B_139 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_8,c_588])).

tff(c_516,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_584,plain,(
    ! [E_125,F_126] :
      ( r2_hidden(k4_tarski(E_125,F_126),k1_xboole_0)
      | ~ r2_hidden(F_126,'#skF_12')
      | ~ r2_hidden(E_125,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_578])).

tff(c_586,plain,(
    ! [F_126,E_125] :
      ( ~ r2_hidden(F_126,'#skF_12')
      | ~ r2_hidden(E_125,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_536,c_584])).

tff(c_697,plain,(
    ! [E_125] : ~ r2_hidden(E_125,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_586])).

tff(c_750,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_742,c_697])).

tff(c_766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_611,c_750])).

tff(c_767,plain,(
    ! [F_126] : ~ r2_hidden(F_126,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_586])).

tff(c_924,plain,(
    '#skF_9' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_908,c_767])).

tff(c_942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_924])).

tff(c_944,plain,(
    ! [F_151] : ~ r2_hidden(F_151,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_959,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_566,c_944])).

tff(c_966,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_59])).

tff(c_1295,plain,(
    ! [B_174] :
      ( r2_hidden('#skF_1'('#skF_10',B_174),B_174)
      | B_174 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_8,c_944])).

tff(c_967,plain,(
    '#skF_11' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_58])).

tff(c_1029,plain,(
    ! [E_156] : ~ r2_hidden(E_156,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_586])).

tff(c_1101,plain,(
    ! [B_161] :
      ( r2_hidden('#skF_1'('#skF_11',B_161),B_161)
      | B_161 = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_8,c_1029])).

tff(c_943,plain,(
    ! [F_126] : ~ r2_hidden(F_126,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_1117,plain,(
    '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1101,c_943])).

tff(c_1128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_967,c_1117])).

tff(c_1129,plain,(
    ! [F_126] : ~ r2_hidden(F_126,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_586])).

tff(c_1315,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1295,c_1129])).

tff(c_1330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_966,c_1315])).

tff(c_1332,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1334,plain,(
    ! [A_4] : k4_xboole_0('#skF_12',A_4) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1332,c_10])).

tff(c_1554,plain,(
    ! [B_206,A_207] :
      ( ~ r2_hidden(B_206,A_207)
      | k4_xboole_0(A_207,k1_tarski(B_206)) != A_207 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1559,plain,(
    ! [B_206] : ~ r2_hidden(B_206,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_1554])).

tff(c_1594,plain,(
    ! [B_212] :
      ( r2_hidden('#skF_1'('#skF_12',B_212),B_212)
      | B_212 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_1587,c_1559])).

tff(c_1628,plain,(
    ! [A_224,B_225,D_226] :
      ( r2_hidden('#skF_7'(A_224,B_225,k2_zfmisc_1(A_224,B_225),D_226),A_224)
      | ~ r2_hidden(D_226,k2_zfmisc_1(A_224,B_225)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1640,plain,(
    ! [D_230,B_231] : ~ r2_hidden(D_230,k2_zfmisc_1('#skF_12',B_231)) ),
    inference(resolution,[status(thm)],[c_1628,c_1559])).

tff(c_1672,plain,(
    ! [B_231] : k2_zfmisc_1('#skF_12',B_231) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1594,c_1640])).

tff(c_1393,plain,(
    ! [A_183,B_184] :
      ( r2_hidden('#skF_1'(A_183,B_184),B_184)
      | r2_hidden('#skF_2'(A_183,B_184),A_183)
      | B_184 = A_183 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1374,plain,(
    ! [B_178,A_179] :
      ( ~ r2_hidden(B_178,A_179)
      | k4_xboole_0(A_179,k1_tarski(B_178)) != A_179 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1383,plain,(
    ! [B_178] : ~ r2_hidden(B_178,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_1374])).

tff(c_1400,plain,(
    ! [B_184] :
      ( r2_hidden('#skF_1'('#skF_12',B_184),B_184)
      | B_184 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_1393,c_1383])).

tff(c_1483,plain,(
    ! [A_200,B_201,D_202] :
      ( r2_hidden('#skF_8'(A_200,B_201,k2_zfmisc_1(A_200,B_201),D_202),B_201)
      | ~ r2_hidden(D_202,k2_zfmisc_1(A_200,B_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1493,plain,(
    ! [D_203,A_204] : ~ r2_hidden(D_203,k2_zfmisc_1(A_204,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_1483,c_1383])).

tff(c_1528,plain,(
    ! [A_204] : k2_zfmisc_1(A_204,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1400,c_1493])).

tff(c_1331,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1339,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1332,c_1331])).

tff(c_1340,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_1339])).

tff(c_40,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1353,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1340,c_1332,c_40])).

tff(c_1535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1353])).

tff(c_1536,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_1339])).

tff(c_1543,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1536,c_1332,c_40])).

tff(c_1679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_1543])).

tff(c_1681,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1680,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1689,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_1681,c_1680])).

tff(c_1690,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1689])).

tff(c_1682,plain,(
    ! [A_4] : k4_xboole_0('#skF_11',A_4) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_1681,c_10])).

tff(c_1701,plain,(
    ! [A_4] : k4_xboole_0('#skF_10',A_4) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_1690,c_1682])).

tff(c_1733,plain,(
    ! [B_235,A_236] :
      ( ~ r2_hidden(B_235,A_236)
      | k4_xboole_0(A_236,k1_tarski(B_235)) != A_236 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1742,plain,(
    ! [B_235] : ~ r2_hidden(B_235,'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1701,c_1733])).

tff(c_1760,plain,(
    ! [B_243] :
      ( r2_hidden('#skF_1'('#skF_10',B_243),B_243)
      | B_243 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1746,c_1742])).

tff(c_1857,plain,(
    ! [A_258,B_259,D_260] :
      ( r2_hidden('#skF_8'(A_258,B_259,k2_zfmisc_1(A_258,B_259),D_260),B_259)
      | ~ r2_hidden(D_260,k2_zfmisc_1(A_258,B_259)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1867,plain,(
    ! [D_261,A_262] : ~ r2_hidden(D_261,k2_zfmisc_1(A_262,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_1857,c_1742])).

tff(c_1908,plain,(
    ! [A_262] : k2_zfmisc_1(A_262,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1760,c_1867])).

tff(c_1692,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_1681])).

tff(c_44,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1710,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_1690,c_1692,c_44])).

tff(c_1914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1908,c_1710])).

tff(c_1915,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1689])).

tff(c_1930,plain,(
    ! [A_4] : k4_xboole_0('#skF_9',A_4) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_1915,c_1682])).

tff(c_1959,plain,(
    ! [B_266,A_267] :
      ( ~ r2_hidden(B_266,A_267)
      | k4_xboole_0(A_267,k1_tarski(B_266)) != A_267 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1968,plain,(
    ! [B_266] : ~ r2_hidden(B_266,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1930,c_1959])).

tff(c_1988,plain,(
    ! [B_274] :
      ( r2_hidden('#skF_1'('#skF_9',B_274),B_274)
      | B_274 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1980,c_1968])).

tff(c_2014,plain,(
    ! [A_282,B_283,D_284] :
      ( r2_hidden('#skF_7'(A_282,B_283,k2_zfmisc_1(A_282,B_283),D_284),A_282)
      | ~ r2_hidden(D_284,k2_zfmisc_1(A_282,B_283)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2020,plain,(
    ! [D_285,B_286] : ~ r2_hidden(D_285,k2_zfmisc_1('#skF_9',B_286)) ),
    inference(resolution,[status(thm)],[c_2014,c_1968])).

tff(c_2047,plain,(
    ! [B_286] : k2_zfmisc_1('#skF_9',B_286) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1988,c_2020])).

tff(c_1918,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_1681])).

tff(c_1939,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_1915,c_1918,c_44])).

tff(c_2065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2047,c_1939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.48  
% 3.01/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.48  %$ r2_hidden > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 3.01/1.48  
% 3.01/1.48  %Foreground sorts:
% 3.01/1.48  
% 3.01/1.48  
% 3.01/1.48  %Background operators:
% 3.01/1.48  
% 3.01/1.48  
% 3.01/1.48  %Foreground operators:
% 3.01/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.48  tff('#skF_11', type, '#skF_11': $i).
% 3.01/1.48  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.01/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.01/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.01/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.01/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.01/1.48  tff('#skF_10', type, '#skF_10': $i).
% 3.01/1.48  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.01/1.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.01/1.48  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.01/1.48  tff('#skF_9', type, '#skF_9': $i).
% 3.01/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.01/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.01/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.01/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.01/1.48  tff('#skF_12', type, '#skF_12': $i).
% 3.01/1.48  
% 3.07/1.50  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.07/1.50  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.07/1.50  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.07/1.50  tff(f_58, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.07/1.50  tff(f_46, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.07/1.50  tff(c_1980, plain, (![A_273, B_274]: (r2_hidden('#skF_1'(A_273, B_274), B_274) | r2_hidden('#skF_2'(A_273, B_274), A_273) | B_274=A_273)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.50  tff(c_1746, plain, (![A_242, B_243]: (r2_hidden('#skF_1'(A_242, B_243), B_243) | r2_hidden('#skF_2'(A_242, B_243), A_242) | B_243=A_242)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.50  tff(c_1587, plain, (![A_211, B_212]: (r2_hidden('#skF_1'(A_211, B_212), B_212) | r2_hidden('#skF_2'(A_211, B_212), A_211) | B_212=A_211)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.50  tff(c_552, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(A_122, B_123), B_123) | r2_hidden('#skF_2'(A_122, B_123), A_122) | B_123=A_122)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.50  tff(c_10, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.07/1.50  tff(c_527, plain, (![B_113, A_114]: (~r2_hidden(B_113, A_114) | k4_xboole_0(A_114, k1_tarski(B_113))!=A_114)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.50  tff(c_536, plain, (![B_113]: (~r2_hidden(B_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_527])).
% 3.07/1.50  tff(c_566, plain, (![B_123]: (r2_hidden('#skF_1'(k1_xboole_0, B_123), B_123) | k1_xboole_0=B_123)), inference(resolution, [status(thm)], [c_552, c_536])).
% 3.07/1.50  tff(c_434, plain, (![A_95, B_96]: (r2_hidden('#skF_1'(A_95, B_96), B_96) | r2_hidden('#skF_2'(A_95, B_96), A_95) | B_96=A_95)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.50  tff(c_223, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), B_67) | r2_hidden('#skF_2'(A_66, B_67), A_66) | B_67=A_66)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.50  tff(c_42, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.07/1.50  tff(c_59, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_42])).
% 3.07/1.50  tff(c_96, plain, (![A_47, B_48]: (r2_hidden('#skF_1'(A_47, B_48), B_48) | r2_hidden('#skF_2'(A_47, B_48), A_47) | B_48=A_47)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.50  tff(c_85, plain, (![B_44, A_45]: (~r2_hidden(B_44, A_45) | k4_xboole_0(A_45, k1_tarski(B_44))!=A_45)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.50  tff(c_94, plain, (![B_44]: (~r2_hidden(B_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_85])).
% 3.07/1.50  tff(c_103, plain, (![B_48]: (r2_hidden('#skF_1'(k1_xboole_0, B_48), B_48) | k1_xboole_0=B_48)), inference(resolution, [status(thm)], [c_96, c_94])).
% 3.07/1.50  tff(c_46, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.07/1.50  tff(c_58, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_46])).
% 3.07/1.50  tff(c_50, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.07/1.50  tff(c_80, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 3.07/1.50  tff(c_136, plain, (![E_56, F_57, A_58, B_59]: (r2_hidden(k4_tarski(E_56, F_57), k2_zfmisc_1(A_58, B_59)) | ~r2_hidden(F_57, B_59) | ~r2_hidden(E_56, A_58))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.50  tff(c_139, plain, (![E_56, F_57]: (r2_hidden(k4_tarski(E_56, F_57), k1_xboole_0) | ~r2_hidden(F_57, '#skF_12') | ~r2_hidden(E_56, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_136])).
% 3.07/1.50  tff(c_140, plain, (![F_57, E_56]: (~r2_hidden(F_57, '#skF_12') | ~r2_hidden(E_56, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_94, c_139])).
% 3.07/1.50  tff(c_142, plain, (![E_60]: (~r2_hidden(E_60, '#skF_11'))), inference(splitLeft, [status(thm)], [c_140])).
% 3.07/1.50  tff(c_150, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_103, c_142])).
% 3.07/1.50  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_150])).
% 3.07/1.50  tff(c_163, plain, (![F_61]: (~r2_hidden(F_61, '#skF_12'))), inference(splitRight, [status(thm)], [c_140])).
% 3.07/1.50  tff(c_171, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_103, c_163])).
% 3.07/1.50  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_171])).
% 3.07/1.50  tff(c_183, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_50])).
% 3.07/1.50  tff(c_185, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_183])).
% 3.07/1.50  tff(c_189, plain, (![A_4]: (k4_xboole_0('#skF_10', A_4)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_185, c_10])).
% 3.07/1.50  tff(c_212, plain, (![B_63, A_64]: (~r2_hidden(B_63, A_64) | k4_xboole_0(A_64, k1_tarski(B_63))!=A_64)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.50  tff(c_220, plain, (![B_63]: (~r2_hidden(B_63, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_212])).
% 3.07/1.50  tff(c_230, plain, (![B_67]: (r2_hidden('#skF_1'('#skF_10', B_67), B_67) | B_67='#skF_10')), inference(resolution, [status(thm)], [c_223, c_220])).
% 3.07/1.50  tff(c_336, plain, (![A_86, B_87, D_88]: (r2_hidden('#skF_8'(A_86, B_87, k2_zfmisc_1(A_86, B_87), D_88), B_87) | ~r2_hidden(D_88, k2_zfmisc_1(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.50  tff(c_346, plain, (![D_89, A_90]: (~r2_hidden(D_89, k2_zfmisc_1(A_90, '#skF_10')))), inference(resolution, [status(thm)], [c_336, c_220])).
% 3.07/1.50  tff(c_387, plain, (![A_90]: (k2_zfmisc_1(A_90, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_230, c_346])).
% 3.07/1.50  tff(c_48, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.07/1.50  tff(c_79, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 3.07/1.50  tff(c_186, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_79])).
% 3.07/1.50  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_387, c_186])).
% 3.07/1.50  tff(c_394, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_183])).
% 3.07/1.50  tff(c_401, plain, (![A_4]: (k4_xboole_0('#skF_9', A_4)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_394, c_394, c_10])).
% 3.07/1.50  tff(c_423, plain, (![B_92, A_93]: (~r2_hidden(B_92, A_93) | k4_xboole_0(A_93, k1_tarski(B_92))!=A_93)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.50  tff(c_431, plain, (![B_92]: (~r2_hidden(B_92, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_401, c_423])).
% 3.07/1.50  tff(c_441, plain, (![B_96]: (r2_hidden('#skF_1'('#skF_9', B_96), B_96) | B_96='#skF_9')), inference(resolution, [status(thm)], [c_434, c_431])).
% 3.07/1.50  tff(c_475, plain, (![A_108, B_109, D_110]: (r2_hidden('#skF_7'(A_108, B_109, k2_zfmisc_1(A_108, B_109), D_110), A_108) | ~r2_hidden(D_110, k2_zfmisc_1(A_108, B_109)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.50  tff(c_481, plain, (![D_111, B_112]: (~r2_hidden(D_111, k2_zfmisc_1('#skF_9', B_112)))), inference(resolution, [status(thm)], [c_475, c_431])).
% 3.07/1.50  tff(c_509, plain, (![B_112]: (k2_zfmisc_1('#skF_9', B_112)='#skF_9')), inference(resolution, [status(thm)], [c_441, c_481])).
% 3.07/1.50  tff(c_398, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_394, c_79])).
% 3.07/1.50  tff(c_515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_509, c_398])).
% 3.07/1.50  tff(c_517, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 3.07/1.50  tff(c_578, plain, (![E_125, F_126, A_127, B_128]: (r2_hidden(k4_tarski(E_125, F_126), k2_zfmisc_1(A_127, B_128)) | ~r2_hidden(F_126, B_128) | ~r2_hidden(E_125, A_127))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.50  tff(c_581, plain, (![E_125, F_126]: (r2_hidden(k4_tarski(E_125, F_126), k1_xboole_0) | ~r2_hidden(F_126, '#skF_10') | ~r2_hidden(E_125, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_517, c_578])).
% 3.07/1.50  tff(c_585, plain, (![F_126, E_125]: (~r2_hidden(F_126, '#skF_10') | ~r2_hidden(E_125, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_536, c_581])).
% 3.07/1.50  tff(c_588, plain, (![E_129]: (~r2_hidden(E_129, '#skF_9'))), inference(splitLeft, [status(thm)], [c_585])).
% 3.07/1.50  tff(c_603, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_566, c_588])).
% 3.07/1.50  tff(c_610, plain, ('#skF_9'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_603, c_59])).
% 3.07/1.50  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.50  tff(c_908, plain, (![B_150]: (r2_hidden('#skF_1'('#skF_9', B_150), B_150) | B_150='#skF_9')), inference(resolution, [status(thm)], [c_8, c_588])).
% 3.07/1.50  tff(c_611, plain, ('#skF_11'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_603, c_58])).
% 3.07/1.50  tff(c_742, plain, (![B_139]: (r2_hidden('#skF_1'('#skF_9', B_139), B_139) | B_139='#skF_9')), inference(resolution, [status(thm)], [c_8, c_588])).
% 3.07/1.50  tff(c_516, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 3.07/1.50  tff(c_584, plain, (![E_125, F_126]: (r2_hidden(k4_tarski(E_125, F_126), k1_xboole_0) | ~r2_hidden(F_126, '#skF_12') | ~r2_hidden(E_125, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_516, c_578])).
% 3.07/1.50  tff(c_586, plain, (![F_126, E_125]: (~r2_hidden(F_126, '#skF_12') | ~r2_hidden(E_125, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_536, c_584])).
% 3.07/1.50  tff(c_697, plain, (![E_125]: (~r2_hidden(E_125, '#skF_11'))), inference(splitLeft, [status(thm)], [c_586])).
% 3.07/1.50  tff(c_750, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_742, c_697])).
% 3.07/1.50  tff(c_766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_611, c_750])).
% 3.07/1.50  tff(c_767, plain, (![F_126]: (~r2_hidden(F_126, '#skF_12'))), inference(splitRight, [status(thm)], [c_586])).
% 3.07/1.50  tff(c_924, plain, ('#skF_9'='#skF_12'), inference(resolution, [status(thm)], [c_908, c_767])).
% 3.07/1.50  tff(c_942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_610, c_924])).
% 3.07/1.50  tff(c_944, plain, (![F_151]: (~r2_hidden(F_151, '#skF_10'))), inference(splitRight, [status(thm)], [c_585])).
% 3.07/1.50  tff(c_959, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_566, c_944])).
% 3.07/1.50  tff(c_966, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_959, c_59])).
% 3.07/1.50  tff(c_1295, plain, (![B_174]: (r2_hidden('#skF_1'('#skF_10', B_174), B_174) | B_174='#skF_10')), inference(resolution, [status(thm)], [c_8, c_944])).
% 3.07/1.50  tff(c_967, plain, ('#skF_11'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_959, c_58])).
% 3.07/1.50  tff(c_1029, plain, (![E_156]: (~r2_hidden(E_156, '#skF_11'))), inference(splitLeft, [status(thm)], [c_586])).
% 3.07/1.50  tff(c_1101, plain, (![B_161]: (r2_hidden('#skF_1'('#skF_11', B_161), B_161) | B_161='#skF_11')), inference(resolution, [status(thm)], [c_8, c_1029])).
% 3.07/1.50  tff(c_943, plain, (![F_126]: (~r2_hidden(F_126, '#skF_10'))), inference(splitRight, [status(thm)], [c_585])).
% 3.07/1.50  tff(c_1117, plain, ('#skF_11'='#skF_10'), inference(resolution, [status(thm)], [c_1101, c_943])).
% 3.07/1.50  tff(c_1128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_967, c_1117])).
% 3.07/1.50  tff(c_1129, plain, (![F_126]: (~r2_hidden(F_126, '#skF_12'))), inference(splitRight, [status(thm)], [c_586])).
% 3.07/1.50  tff(c_1315, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_1295, c_1129])).
% 3.07/1.50  tff(c_1330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_966, c_1315])).
% 3.07/1.50  tff(c_1332, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_42])).
% 3.07/1.50  tff(c_1334, plain, (![A_4]: (k4_xboole_0('#skF_12', A_4)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1332, c_10])).
% 3.07/1.50  tff(c_1554, plain, (![B_206, A_207]: (~r2_hidden(B_206, A_207) | k4_xboole_0(A_207, k1_tarski(B_206))!=A_207)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.50  tff(c_1559, plain, (![B_206]: (~r2_hidden(B_206, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1334, c_1554])).
% 3.07/1.50  tff(c_1594, plain, (![B_212]: (r2_hidden('#skF_1'('#skF_12', B_212), B_212) | B_212='#skF_12')), inference(resolution, [status(thm)], [c_1587, c_1559])).
% 3.07/1.50  tff(c_1628, plain, (![A_224, B_225, D_226]: (r2_hidden('#skF_7'(A_224, B_225, k2_zfmisc_1(A_224, B_225), D_226), A_224) | ~r2_hidden(D_226, k2_zfmisc_1(A_224, B_225)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.50  tff(c_1640, plain, (![D_230, B_231]: (~r2_hidden(D_230, k2_zfmisc_1('#skF_12', B_231)))), inference(resolution, [status(thm)], [c_1628, c_1559])).
% 3.07/1.50  tff(c_1672, plain, (![B_231]: (k2_zfmisc_1('#skF_12', B_231)='#skF_12')), inference(resolution, [status(thm)], [c_1594, c_1640])).
% 3.07/1.50  tff(c_1393, plain, (![A_183, B_184]: (r2_hidden('#skF_1'(A_183, B_184), B_184) | r2_hidden('#skF_2'(A_183, B_184), A_183) | B_184=A_183)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.07/1.50  tff(c_1374, plain, (![B_178, A_179]: (~r2_hidden(B_178, A_179) | k4_xboole_0(A_179, k1_tarski(B_178))!=A_179)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.50  tff(c_1383, plain, (![B_178]: (~r2_hidden(B_178, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1334, c_1374])).
% 3.07/1.50  tff(c_1400, plain, (![B_184]: (r2_hidden('#skF_1'('#skF_12', B_184), B_184) | B_184='#skF_12')), inference(resolution, [status(thm)], [c_1393, c_1383])).
% 3.07/1.50  tff(c_1483, plain, (![A_200, B_201, D_202]: (r2_hidden('#skF_8'(A_200, B_201, k2_zfmisc_1(A_200, B_201), D_202), B_201) | ~r2_hidden(D_202, k2_zfmisc_1(A_200, B_201)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.50  tff(c_1493, plain, (![D_203, A_204]: (~r2_hidden(D_203, k2_zfmisc_1(A_204, '#skF_12')))), inference(resolution, [status(thm)], [c_1483, c_1383])).
% 3.07/1.50  tff(c_1528, plain, (![A_204]: (k2_zfmisc_1(A_204, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_1400, c_1493])).
% 3.07/1.50  tff(c_1331, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_42])).
% 3.07/1.50  tff(c_1339, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1332, c_1331])).
% 3.07/1.50  tff(c_1340, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_1339])).
% 3.07/1.50  tff(c_40, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.07/1.50  tff(c_1353, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1340, c_1332, c_40])).
% 3.07/1.50  tff(c_1535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1528, c_1353])).
% 3.07/1.50  tff(c_1536, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_1339])).
% 3.07/1.50  tff(c_1543, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1536, c_1332, c_40])).
% 3.07/1.50  tff(c_1679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1672, c_1543])).
% 3.07/1.50  tff(c_1681, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_46])).
% 3.07/1.50  tff(c_1680, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_46])).
% 3.07/1.50  tff(c_1689, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_1681, c_1680])).
% 3.07/1.50  tff(c_1690, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_1689])).
% 3.07/1.50  tff(c_1682, plain, (![A_4]: (k4_xboole_0('#skF_11', A_4)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_1681, c_10])).
% 3.07/1.50  tff(c_1701, plain, (![A_4]: (k4_xboole_0('#skF_10', A_4)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_1690, c_1682])).
% 3.07/1.50  tff(c_1733, plain, (![B_235, A_236]: (~r2_hidden(B_235, A_236) | k4_xboole_0(A_236, k1_tarski(B_235))!=A_236)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.50  tff(c_1742, plain, (![B_235]: (~r2_hidden(B_235, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1701, c_1733])).
% 3.07/1.50  tff(c_1760, plain, (![B_243]: (r2_hidden('#skF_1'('#skF_10', B_243), B_243) | B_243='#skF_10')), inference(resolution, [status(thm)], [c_1746, c_1742])).
% 3.07/1.50  tff(c_1857, plain, (![A_258, B_259, D_260]: (r2_hidden('#skF_8'(A_258, B_259, k2_zfmisc_1(A_258, B_259), D_260), B_259) | ~r2_hidden(D_260, k2_zfmisc_1(A_258, B_259)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.50  tff(c_1867, plain, (![D_261, A_262]: (~r2_hidden(D_261, k2_zfmisc_1(A_262, '#skF_10')))), inference(resolution, [status(thm)], [c_1857, c_1742])).
% 3.07/1.50  tff(c_1908, plain, (![A_262]: (k2_zfmisc_1(A_262, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1760, c_1867])).
% 3.07/1.50  tff(c_1692, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_1681])).
% 3.07/1.50  tff(c_44, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.07/1.50  tff(c_1710, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_1690, c_1692, c_44])).
% 3.07/1.50  tff(c_1914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1908, c_1710])).
% 3.07/1.50  tff(c_1915, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_1689])).
% 3.07/1.50  tff(c_1930, plain, (![A_4]: (k4_xboole_0('#skF_9', A_4)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1915, c_1915, c_1682])).
% 3.07/1.50  tff(c_1959, plain, (![B_266, A_267]: (~r2_hidden(B_266, A_267) | k4_xboole_0(A_267, k1_tarski(B_266))!=A_267)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.50  tff(c_1968, plain, (![B_266]: (~r2_hidden(B_266, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1930, c_1959])).
% 3.07/1.50  tff(c_1988, plain, (![B_274]: (r2_hidden('#skF_1'('#skF_9', B_274), B_274) | B_274='#skF_9')), inference(resolution, [status(thm)], [c_1980, c_1968])).
% 3.07/1.50  tff(c_2014, plain, (![A_282, B_283, D_284]: (r2_hidden('#skF_7'(A_282, B_283, k2_zfmisc_1(A_282, B_283), D_284), A_282) | ~r2_hidden(D_284, k2_zfmisc_1(A_282, B_283)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.50  tff(c_2020, plain, (![D_285, B_286]: (~r2_hidden(D_285, k2_zfmisc_1('#skF_9', B_286)))), inference(resolution, [status(thm)], [c_2014, c_1968])).
% 3.07/1.50  tff(c_2047, plain, (![B_286]: (k2_zfmisc_1('#skF_9', B_286)='#skF_9')), inference(resolution, [status(thm)], [c_1988, c_2020])).
% 3.07/1.50  tff(c_1918, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1915, c_1681])).
% 3.07/1.50  tff(c_1939, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1918, c_1915, c_1918, c_44])).
% 3.07/1.50  tff(c_2065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2047, c_1939])).
% 3.07/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.50  
% 3.07/1.50  Inference rules
% 3.07/1.50  ----------------------
% 3.07/1.50  #Ref     : 0
% 3.07/1.50  #Sup     : 381
% 3.07/1.50  #Fact    : 0
% 3.07/1.50  #Define  : 0
% 3.07/1.50  #Split   : 13
% 3.07/1.50  #Chain   : 0
% 3.07/1.50  #Close   : 0
% 3.07/1.50  
% 3.07/1.50  Ordering : KBO
% 3.07/1.50  
% 3.07/1.50  Simplification rules
% 3.07/1.50  ----------------------
% 3.07/1.50  #Subsume      : 123
% 3.07/1.50  #Demod        : 145
% 3.07/1.50  #Tautology    : 132
% 3.07/1.50  #SimpNegUnit  : 31
% 3.07/1.50  #BackRed      : 46
% 3.07/1.50  
% 3.07/1.50  #Partial instantiations: 0
% 3.07/1.50  #Strategies tried      : 1
% 3.07/1.50  
% 3.07/1.50  Timing (in seconds)
% 3.07/1.50  ----------------------
% 3.07/1.51  Preprocessing        : 0.29
% 3.07/1.51  Parsing              : 0.14
% 3.07/1.51  CNF conversion       : 0.03
% 3.07/1.51  Main loop            : 0.43
% 3.07/1.51  Inferencing          : 0.18
% 3.07/1.51  Reduction            : 0.11
% 3.07/1.51  Demodulation         : 0.07
% 3.07/1.51  BG Simplification    : 0.02
% 3.07/1.51  Subsumption          : 0.07
% 3.07/1.51  Abstraction          : 0.02
% 3.07/1.51  MUC search           : 0.00
% 3.07/1.51  Cooper               : 0.00
% 3.07/1.51  Total                : 0.78
% 3.07/1.51  Index Insertion      : 0.00
% 3.07/1.51  Index Deletion       : 0.00
% 3.07/1.51  Index Matching       : 0.00
% 3.07/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
